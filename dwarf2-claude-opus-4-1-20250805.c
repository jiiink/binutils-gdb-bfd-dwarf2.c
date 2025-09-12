/* DWARF 2 support.
   Copyright (C) 1994-2025 Free Software Foundation, Inc.

   Adapted from gdb/dwarf2read.c by Gavin Koch of Cygnus Solutions
   (gavin@cygnus.com).

   From the dwarf2read.c header:
   Adapted by Gary Funck (gary@intrepid.com), Intrepid Technology,
   Inc.  with support from Florida State University (under contract
   with the Ada Joint Program Office), and Silicon Graphics, Inc.
   Initial contribution by Brent Benson, Harris Computer Systems, Inc.,
   based on Fred Fish's (Cygnus Support) implementation of DWARF 1
   support in dwarfread.c

   This file is part of BFD.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or (at
   your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston,
   MA 02110-1301, USA.  */

#include "sysdep.h"
#include "bfd.h"
#include "libiberty.h"
#include "demangle.h"
#include "libbfd.h"
#include "elf-bfd.h"
#include "dwarf2.h"
#include "hashtab.h"
#include "splay-tree.h"

/* The data in the .debug_line statement prologue looks like this.  */

struct line_head
{
  bfd_vma total_length;
  unsigned short version;
  bfd_vma prologue_length;
  unsigned char minimum_instruction_length;
  unsigned char maximum_ops_per_insn;
  unsigned char default_is_stmt;
  int line_base;
  unsigned char line_range;
  unsigned char opcode_base;
  unsigned char *standard_opcode_lengths;
};

/* Attributes have a name and a value.  */

struct attribute
{
  enum dwarf_attribute name;
  enum dwarf_form form;
  union
  {
    char *str;
    struct dwarf_block *blk;
    uint64_t val;
    int64_t sval;
  }
  u;
};

/* Blocks are a bunch of untyped bytes.  */
struct dwarf_block
{
  unsigned int size;
  bfd_byte *data;
};

struct adjusted_section
{
  asection *section;
  bfd_vma adj_vma;
  bfd_vma orig_vma;
};

/* A trie to map quickly from address range to compilation unit.

   This is a fairly standard radix-256 trie, used to quickly locate which
   compilation unit any given address belongs to.  Given that each compilation
   unit may register hundreds of very small and unaligned ranges (which may
   potentially overlap, due to inlining and other concerns), and a large
   program may end up containing hundreds of thousands of such ranges, we cannot
   scan through them linearly without undue slowdown.

   We use a hybrid trie to avoid memory explosion: There are two types of trie
   nodes, leaves and interior nodes.  (Almost all nodes are leaves, so they
   take up the bulk of the memory usage.) Leaves contain a simple array of
   ranges (high/low address) and which compilation unit contains those ranges,
   and when we get to a leaf, we scan through it linearly.  Interior nodes
   contain pointers to 256 other nodes, keyed by the next byte of the address.
   So for a 64-bit address like 0x1234567abcd, we would start at the root and go
   down child[0x00]->child[0x00]->child[0x01]->child[0x23]->child[0x45] etc.,
   until we hit a leaf.  (Nodes are, in general, leaves until they exceed the
   default allocation of 16 elements, at which point they are converted to
   interior node if possible.) This gives us near-constant lookup times;
   the only thing that can be costly is if there are lots of overlapping ranges
   within a single 256-byte segment of the binary, in which case we have to
   scan through them all to find the best match.

   For a binary with few ranges, we will in practice only have a single leaf
   node at the root, containing a simple array.  Thus, the scheme is efficient
   for both small and large binaries.
 */

/* Experiments have shown 16 to be a memory-efficient default leaf size.
   The only case where a leaf will hold more memory than this, is at the
   bottomost level (covering 256 bytes in the binary), where we'll expand
   the leaf to be able to hold more ranges if needed.
 */
#define TRIE_LEAF_SIZE 16

/* All trie_node pointers will really be trie_leaf or trie_interior,
   but they have this common head.  */
struct trie_node
{
  /* If zero, we are an interior node.
     Otherwise, how many ranges we have room for in this leaf.  */
  unsigned int num_room_in_leaf;
};

struct trie_leaf
{
  struct trie_node head;
  unsigned int num_stored_in_leaf;
  struct {
    struct comp_unit *unit;
    bfd_vma low_pc, high_pc;
  } ranges[];
};

struct trie_interior
{
  struct trie_node head;
  struct trie_node *children[256];
};

static struct trie_node *alloc_trie_leaf(bfd *abfd)
{
  if (abfd == NULL)
    return NULL;
    
  size_t amt = sizeof(struct trie_leaf) + TRIE_LEAF_SIZE * sizeof(((struct trie_leaf *)0)->ranges[0]);
  
  struct trie_leaf *leaf = bfd_zalloc(abfd, amt);
  if (leaf == NULL)
    return NULL;
    
  leaf->head.num_room_in_leaf = TRIE_LEAF_SIZE;
  return &leaf->head;
}

struct addr_range
{
  bfd_byte *start;
  bfd_byte *end;
};

/* Return true if address range do intersect.  */

static bool addr_range_intersects(struct addr_range *r1, struct addr_range *r2)
{
    if (r1 == NULL || r2 == NULL) {
        return false;
    }
    
    if (r1->end <= r1->start || r2->end <= r2->start) {
        return false;
    }
    
    return (r1->start < r2->end) && (r2->start < r1->end);
}

/* Compare function for splay tree of addr_ranges.  */

static int
splay_tree_compare_addr_range (splay_tree_key xa, splay_tree_key xb)
{
  if (xa == NULL || xb == NULL) {
    return 0;
  }
  
  const struct addr_range *r1 = (const struct addr_range *) xa;
  const struct addr_range *r2 = (const struct addr_range *) xb;

  if (addr_range_intersects (r1, r2) || addr_range_intersects (r2, r1)) {
    return 0;
  }
  
  if (r1->end <= r2->start) {
    return -1;
  }
  
  return 1;
}

/* Splay tree release function for keys (addr_range).  */

static void splay_tree_free_addr_range(splay_tree_key key)
{
    if (key != NULL) {
        free((struct addr_range *)key);
    }
}

struct dwarf2_debug_file
{
  /* The actual bfd from which debug info was loaded.  Might be
     different to orig_bfd because of gnu_debuglink sections.  */
  bfd *bfd_ptr;

  /* Pointer to the symbol table.  */
  asymbol **syms;

  /* The current info pointer for the .debug_info section being parsed.  */
  bfd_byte *info_ptr;

  /* A pointer to the memory block allocated for .debug_info sections.  */
  bfd_byte *dwarf_info_buffer;

  /* Length of the loaded .debug_info sections.  */
  bfd_size_type dwarf_info_size;

  /* Pointer to the .debug_abbrev section loaded into memory.  */
  bfd_byte *dwarf_abbrev_buffer;

  /* Length of the loaded .debug_abbrev section.  */
  bfd_size_type dwarf_abbrev_size;

  /* Buffer for decode_line_info.  */
  bfd_byte *dwarf_line_buffer;

  /* Length of the loaded .debug_line section.  */
  bfd_size_type dwarf_line_size;

  /* Pointer to the .debug_str section loaded into memory.  */
  bfd_byte *dwarf_str_buffer;

  /* Length of the loaded .debug_str section.  */
  bfd_size_type dwarf_str_size;

  /* Pointer to the .debug_str_offsets section loaded into memory.  */
  bfd_byte *dwarf_str_offsets_buffer;

  /* Length of the loaded .debug_str_offsets section.  */
  bfd_size_type dwarf_str_offsets_size;

  /* Pointer to the .debug_addr section loaded into memory.  */
  bfd_byte *dwarf_addr_buffer;

  /* Length of the loaded .debug_addr section.  */
  bfd_size_type dwarf_addr_size;

  /* Pointer to the .debug_line_str section loaded into memory.  */
  bfd_byte *dwarf_line_str_buffer;

  /* Length of the loaded .debug_line_str section.  */
  bfd_size_type dwarf_line_str_size;

  /* Pointer to the .debug_ranges section loaded into memory.  */
  bfd_byte *dwarf_ranges_buffer;

  /* Length of the loaded .debug_ranges section.  */
  bfd_size_type dwarf_ranges_size;

  /* Pointer to the .debug_rnglists section loaded into memory.  */
  bfd_byte *dwarf_rnglists_buffer;

  /* Length of the loaded .debug_rnglists section.  */
  bfd_size_type dwarf_rnglists_size;

  /* A list of all previously read comp_units.  */
  struct comp_unit *all_comp_units;

  /* A list of all previously read comp_units with no ranges (yet).  */
  struct comp_unit *all_comp_units_without_ranges;

  /* Last comp unit in list above.  */
  struct comp_unit *last_comp_unit;

  /* Line table at line_offset zero.  */
  struct line_info_table *line_table;

  /* Hash table to map offsets to decoded abbrevs.  */
  htab_t abbrev_offsets;

  /* Root of a trie to map addresses to compilation units.  */
  struct trie_node *trie_root;

  /* Splay tree to map info_ptr address to compilation units.  */
  splay_tree comp_unit_tree;
};

struct dwarf2_debug
{
  /* Names of the debug sections.  */
  const struct dwarf_debug_section *debug_sections;

  /* Per-file stuff.  */
  struct dwarf2_debug_file f, alt;

  /* If the most recent call to bfd_find_nearest_line was given an
     address in an inlined function, preserve a pointer into the
     calling chain for subsequent calls to bfd_find_inliner_info to
     use.  */
  struct funcinfo *inliner_chain;

  /* Section VMAs at the time the stash was built.  */
  bfd_vma *sec_vma;
  /* Number of sections in the SEC_VMA table.  */
  unsigned int sec_vma_count;

  /* Number of sections whose VMA we must adjust.  */
  int adjusted_section_count;

  /* Array of sections with adjusted VMA.  */
  struct adjusted_section *adjusted_sections;

  /* Used to validate the cached debug data.  */
  unsigned int orig_bfd_id;

  /* Number of times find_line is called.  This is used in
     the heuristic for enabling the info hash tables.  */
  int info_hash_count;

#define STASH_INFO_HASH_TRIGGER    100

  /* Hash table mapping symbol names to function infos.  */
  struct info_hash_table *funcinfo_hash_table;

  /* Hash table mapping symbol names to variable infos.  */
  struct info_hash_table *varinfo_hash_table;

  /* Head of comp_unit list in the last hash table update.  */
  struct comp_unit *hash_units_head;

  /* Status of info hash.  */
  int info_hash_status;
#define STASH_INFO_HASH_OFF	   0
#define STASH_INFO_HASH_ON	   1
#define STASH_INFO_HASH_DISABLED   2

  /* True if we opened bfd_ptr.  */
  bool close_on_cleanup;
};

struct arange
{
  struct arange *next;
  bfd_vma low;
  bfd_vma high;
};

/* A minimal decoding of DWARF2 compilation units.  We only decode
   what's needed to get to the line number information.  */

struct comp_unit
{
  /* Chain the previously read compilation units.  */
  struct comp_unit *next_unit;

  /* Chain the previously read compilation units that have no ranges yet.
     We scan these separately when we have a trie over the ranges.
     Unused if arange.high != 0. */
  struct comp_unit *next_unit_without_ranges;

  /* Likewise, chain the compilation unit read after this one.
     The comp units are stored in reversed reading order.  */
  struct comp_unit *prev_unit;

  /* Keep the bfd convenient (for memory allocation).  */
  bfd *abfd;

  /* The lowest and highest addresses contained in this compilation
     unit as specified in the compilation unit header.  */
  struct arange arange;

  /* The DW_AT_name attribute (for error messages).  */
  char *name;

  /* The abbrev hash table.  */
  struct abbrev_info **abbrevs;

  /* DW_AT_language.  */
  int lang;

  /* Note that an error was found by comp_unit_find_nearest_line.  */
  int error;

  /* The DW_AT_comp_dir attribute.  */
  char *comp_dir;

  /* TRUE if there is a line number table associated with this comp. unit.  */
  int stmtlist;

  /* Pointer to the current comp_unit so that we can find a given entry
     by its reference.  */
  bfd_byte *info_ptr_unit;

  /* The offset into .debug_line of the line number table.  */
  unsigned long line_offset;

  /* Pointer to the first child die for the comp unit.  */
  bfd_byte *first_child_die_ptr;

  /* The end of the comp unit.  */
  bfd_byte *end_ptr;

  /* The decoded line number, NULL if not yet decoded.  */
  struct line_info_table *line_table;

  /* A list of the functions found in this comp. unit.  */
  struct funcinfo *function_table;

  /* A table of function information references searchable by address.  */
  struct lookup_funcinfo *lookup_funcinfo_table;

  /* Number of functions in the function_table and sorted_function_table.  */
  bfd_size_type number_of_functions;

  /* A list of the variables found in this comp. unit.  */
  struct varinfo *variable_table;

  /* Pointers to dwarf2_debug structures.  */
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;

  /* DWARF format version for this unit - from unit header.  */
  int version;

  /* Address size for this unit - from unit header.  */
  unsigned char addr_size;

  /* Offset size for this unit - from unit header.  */
  unsigned char offset_size;

  /* Base address for this unit - from DW_AT_low_pc attribute of
     DW_TAG_compile_unit DIE */
  bfd_vma base_address;

  /* TRUE if symbols are cached in hash table for faster lookup by name.  */
  bool cached;

  /* Used when iterating over trie leaves to know which units we have
     already seen in this iteration.  */
  bool mark;

 /* Base address of debug_addr section.  */
  size_t dwarf_addr_offset;

  /* Base address of string offset table.  */
  size_t dwarf_str_offset;
};

/* This data structure holds the information of an abbrev.  */
struct abbrev_info
{
  unsigned int         number;		/* Number identifying abbrev.  */
  enum dwarf_tag       tag;		/* DWARF tag.  */
  bool                 has_children;	/* TRUE if the abbrev has children.  */
  unsigned int         num_attrs;	/* Number of attributes.  */
  struct attr_abbrev * attrs;		/* An array of attribute descriptions.  */
  struct abbrev_info * next;		/* Next in chain.  */
};

struct attr_abbrev
{
  enum dwarf_attribute name;
  enum dwarf_form form;
  bfd_vma implicit_const;
};

/* Map of uncompressed DWARF debug section name to compressed one.  It
   is terminated by NULL uncompressed_name.  */

const struct dwarf_debug_section dwarf_debug_sections[] =
{
  { ".debug_abbrev",		".zdebug_abbrev" },
  { ".debug_aranges",		".zdebug_aranges" },
  { ".debug_frame",		".zdebug_frame" },
  { ".debug_info",		".zdebug_info" },
  { ".debug_info",		".zdebug_info" },
  { ".debug_line",		".zdebug_line" },
  { ".debug_loc",		".zdebug_loc" },
  { ".debug_macinfo",		".zdebug_macinfo" },
  { ".debug_macro",		".zdebug_macro" },
  { ".debug_pubnames",		".zdebug_pubnames" },
  { ".debug_pubtypes",		".zdebug_pubtypes" },
  { ".debug_ranges",		".zdebug_ranges" },
  { ".debug_rnglists",		".zdebug_rnglist" },
  { ".debug_static_func",	".zdebug_static_func" },
  { ".debug_static_vars",	".zdebug_static_vars" },
  { ".debug_str",		".zdebug_str", },
  { ".debug_str",		".zdebug_str", },
  { ".debug_str_offsets",	".zdebug_str_offsets", },
  { ".debug_addr",		".zdebug_addr", },
  { ".debug_line_str",		".zdebug_line_str", },
  { ".debug_types",		".zdebug_types" },
  /* GNU DWARF 1 extensions */
  { ".debug_sfnames",		".zdebug_sfnames" },
  { ".debug_srcinfo",		".zebug_srcinfo" },
  /* SGI/MIPS DWARF 2 extensions */
  { ".debug_funcnames",		".zdebug_funcnames" },
  { ".debug_typenames",		".zdebug_typenames" },
  { ".debug_varnames",		".zdebug_varnames" },
  { ".debug_weaknames",		".zdebug_weaknames" },
  { NULL,			NULL },
};

/* NB/ Numbers in this enum must match up with indices
   into the dwarf_debug_sections[] array above.  */
enum dwarf_debug_section_enum
{
  debug_abbrev = 0,
  debug_aranges,
  debug_frame,
  debug_info,
  debug_info_alt,
  debug_line,
  debug_loc,
  debug_macinfo,
  debug_macro,
  debug_pubnames,
  debug_pubtypes,
  debug_ranges,
  debug_rnglists,
  debug_static_func,
  debug_static_vars,
  debug_str,
  debug_str_alt,
  debug_str_offsets,
  debug_addr,
  debug_line_str,
  debug_types,
  debug_sfnames,
  debug_srcinfo,
  debug_funcnames,
  debug_typenames,
  debug_varnames,
  debug_weaknames,
  debug_max
};

/* A static assertion.  */
extern int dwarf_debug_section_assert[ARRAY_SIZE (dwarf_debug_sections)
				      == debug_max + 1 ? 1 : -1];

#ifndef ABBREV_HASH_SIZE
#define ABBREV_HASH_SIZE 121
#endif
#ifndef ATTR_ALLOC_CHUNK
#define ATTR_ALLOC_CHUNK 4
#endif

/* Variable and function hash tables.  This is used to speed up look-up
   in lookup_symbol_in_var_table() and lookup_symbol_in_function_table().
   In order to share code between variable and function infos, we use
   a list of untyped pointer for all variable/function info associated with
   a symbol.  We waste a bit of memory for list with one node but that
   simplifies the code.  */

struct info_list_node
{
  struct info_list_node *next;
  void *info;
};

/* Info hash entry.  */
struct info_hash_entry
{
  struct bfd_hash_entry root;
  struct info_list_node *head;
};

struct info_hash_table
{
  struct bfd_hash_table base;
};

/* Function to create a new entry in info hash table.  */

static struct bfd_hash_entry *
info_hash_table_newfunc (struct bfd_hash_entry *entry,
			 struct bfd_hash_table *table,
			 const char *string)
{
  struct info_hash_entry *ret = (struct info_hash_entry *) entry;

  if (ret == NULL)
    {
      ret = (struct info_hash_entry *) bfd_hash_allocate (table,
							  sizeof (struct info_hash_entry));
      if (ret == NULL)
	return NULL;
    }

  struct bfd_hash_entry *base_entry = bfd_hash_newfunc ((struct bfd_hash_entry *) ret, table, string);
  if (base_entry == NULL)
    return NULL;

  ret = (struct info_hash_entry *) base_entry;
  ret->head = NULL;

  return (struct bfd_hash_entry *) ret;
}

/* Function to create a new info hash table.  It returns a pointer to the
   newly created table or NULL if there is any error.  We need abfd
   solely for memory allocation.  */

static struct info_hash_table *
create_info_hash_table (bfd *abfd)
{
  struct info_hash_table *hash_table;

  if (abfd == NULL)
    return NULL;

  hash_table = (struct info_hash_table *)
		bfd_alloc (abfd, sizeof (struct info_hash_table));
  if (hash_table == NULL)
    return NULL;

  if (!bfd_hash_table_init (&hash_table->base, info_hash_table_newfunc,
			    sizeof (struct info_hash_entry)))
    {
      bfd_release (abfd, hash_table);
      return NULL;
    }

  return hash_table;
}

/* Insert an info entry into an info hash table.  We do not check of
   duplicate entries.  Also, the caller need to guarantee that the
   right type of info in inserted as info is passed as a void* pointer.
   This function returns true if there is no error.  */

static bool
insert_info_hash_table (struct info_hash_table *hash_table,
			const char *key,
			void *info,
			bool copy_p)
{
  if (hash_table == NULL || key == NULL || info == NULL)
    return false;

  struct info_hash_entry *entry = (struct info_hash_entry*) bfd_hash_lookup (&hash_table->base,
						     key, true, copy_p);
  if (entry == NULL)
    return false;

  struct info_list_node *node = (struct info_list_node *) bfd_hash_allocate (&hash_table->base,
						      sizeof (*node));
  if (node == NULL)
    return false;

  node->info = info;
  node->next = entry->head;
  entry->head = node;

  return true;
}

/* Look up an info entry list from an info hash table.  Return NULL
   if there is none.  */

static struct info_list_node *
lookup_info_hash_table (struct info_hash_table *hash_table, const char *key)
{
  struct info_hash_entry *entry;

  if (hash_table == NULL || key == NULL)
    return NULL;

  entry = (struct info_hash_entry*) bfd_hash_lookup (&hash_table->base, key,
						     false, false);
  if (entry == NULL)
    return NULL;
    
  return entry->head;
}

/* Read a section into its appropriate place in the dwarf2_debug
   struct (indicated by SECTION_BUFFER and SECTION_SIZE).  If SYMS is
   not NULL, use bfd_simple_get_relocated_section_contents to read the
   section contents, otherwise use bfd_get_section_contents.  Fail if
   the located section does not contain at least OFFSET bytes.  */

static bool
read_section (bfd *abfd,
              const struct dwarf_debug_section *sec,
              asymbol **syms,
              uint64_t offset,
              bfd_byte **section_buffer,
              bfd_size_type *section_size)
{
  if (*section_buffer != NULL)
    {
      if (offset != 0 && offset >= *section_size)
        {
          _bfd_error_handler (_("DWARF error: offset (%" PRIu64 ")"
                                " greater than or equal to %s size (%" PRIu64 ")"),
                              (uint64_t) offset, sec->uncompressed_name,
                              (uint64_t) *section_size);
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
      return true;
    }

  asection *msec = bfd_get_section_by_name (abfd, sec->uncompressed_name);
  const char *section_name = sec->uncompressed_name;
  
  if (msec == NULL)
    {
      section_name = sec->compressed_name;
      msec = bfd_get_section_by_name (abfd, section_name);
    }
  
  if (msec == NULL)
    {
      _bfd_error_handler (_("DWARF error: can't find %s section."),
                          sec->uncompressed_name);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if ((msec->flags & SEC_HAS_CONTENTS) == 0)
    {
      _bfd_error_handler (_("DWARF error: section %s has no contents"),
                          section_name);
      bfd_set_error (bfd_error_no_contents);
      return false;
    }

  if (bfd_section_size_insane (abfd, msec))
    {
      _bfd_error_handler (_("DWARF error: section %s is too big"),
                          section_name);
      return false;
    }

  bfd_size_type amt = bfd_get_section_limit_octets (abfd, msec);
  *section_size = amt;
  
  amt += 1;
  if (amt == 0)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }
  
  bfd_byte *contents = (bfd_byte *) bfd_malloc (amt);
  if (contents == NULL)
    return false;
  
  bool result = syms
                ? bfd_simple_get_relocated_section_contents (abfd, msec, contents, syms)
                : bfd_get_section_contents (abfd, msec, contents, 0, *section_size);
  
  if (!result)
    {
      free (contents);
      return false;
    }
  
  contents[*section_size] = 0;
  *section_buffer = contents;

  if (offset != 0 && offset >= *section_size)
    {
      _bfd_error_handler (_("DWARF error: offset (%" PRIu64 ")"
                            " greater than or equal to %s size (%" PRIu64 ")"),
                          (uint64_t) offset, section_name,
                          (uint64_t) *section_size);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  return true;
}

/* Read dwarf information from a buffer.  */

static inline uint64_t
read_n_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end, int n)
{
  bfd_byte *buf;
  
  if (ptr == NULL || *ptr == NULL || end == NULL || abfd == NULL)
    return 0;
    
  if (n <= 0 || n > 8)
    return 0;
    
  buf = *ptr;
  
  if (buf > end)
    return 0;
    
  if ((size_t)(end - buf) < (size_t)n)
    {
      *ptr = end;
      return 0;
    }
    
  *ptr = buf + n;
  return bfd_get (n * 8, abfd, buf);
}

static unsigned int
read_1_byte (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return 0;
  
  if (*ptr >= end)
    return 0;
  
  unsigned int result = **ptr;
  (*ptr)++;
  return result;
}

static int
read_1_signed_byte (bfd *abfd ATTRIBUTE_UNUSED, bfd_byte **ptr, bfd_byte *end)
{
  bfd_byte *buf;
  
  if (ptr == NULL || *ptr == NULL || end == NULL)
    return 0;
    
  buf = *ptr;
  
  if (end <= buf)
    {
      *ptr = end;
      return 0;
    }
    
  *ptr = buf + 1;
  return bfd_get_signed_8 (abfd, buf);
}

static unsigned int
read_2_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return 0;
  
  if (*ptr > end || end - *ptr < 2)
    return 0;
  
  return read_n_bytes (abfd, ptr, end, 2);
}

static unsigned int
read_3_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  unsigned int byte1 = read_1_byte (abfd, ptr, end);
  unsigned int byte2 = read_1_byte (abfd, ptr, end);
  unsigned int byte3 = read_1_byte (abfd, ptr, end);
  
  if (bfd_little_endian (abfd))
    return (byte3 << 16) | (byte2 << 8) | byte1;
  
  return (byte1 << 16) | (byte2 << 8) | byte3;
}

static unsigned int
read_4_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return 0;
  
  if (*ptr > end || (end - *ptr) < 4)
    return 0;
  
  return read_n_bytes (abfd, ptr, end, 4);
}

static uint64_t
read_8_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return 0;
  
  if (*ptr > end || (size_t)(end - *ptr) < 8)
    return 0;
  
  return read_n_bytes (abfd, ptr, end, 8);
}

static struct dwarf_block *
read_blk (bfd *abfd, bfd_byte **ptr, bfd_byte *end, size_t size)
{
  struct dwarf_block *block;
  bfd_byte *buf;

  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return NULL;

  buf = *ptr;
  
  if (buf > end)
    return NULL;

  block = (struct dwarf_block *) bfd_alloc (abfd, sizeof (*block));
  if (block == NULL)
    return NULL;

  if (size > (size_t) (end - buf))
    {
      *ptr = end;
      block->data = NULL;
      block->size = 0;
      return block;
    }
  
  *ptr = buf + size;
  block->data = buf;
  block->size = size;
  return block;
}

/* Scans a NUL terminated string starting at *PTR, returning a pointer to it.
   Bytes at or beyond BUF_END will not be read.  Returns NULL if the
   terminator is not found or if the string is empty.  *PTR is
   incremented over the bytes scanned, including the terminator.  */

static char *
read_string (bfd_byte **ptr,
	     bfd_byte *buf_end)
{
  if (ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  bfd_byte *buf = *ptr;
  
  if (buf >= buf_end)
    return NULL;

  bfd_byte *str = buf;

  while (buf < buf_end)
    {
      if (*buf == 0)
        {
          buf++;
          *ptr = buf;
          if (str == buf - 1)
            return NULL;
          return (char *) str;
        }
      buf++;
    }

  *ptr = buf;
  return NULL;
}

/* Reads an offset from *PTR and then locates the string at this offset
   inside the debug string section.  Returns a pointer to the string.
   Increments *PTR by the number of bytes read for the offset.  This
   value is set even if the function fails.  Bytes at or beyond
   BUF_END will not be read.  Returns NULL if there was a problem, or
   if the string is empty.  Does not check for NUL termination of the
   string.  */

static char *
read_indirect_string (struct comp_unit *unit,
		      bfd_byte **ptr,
		      bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  char *str;

  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  stash = unit->stash;
  file = unit->file;

  if (stash == NULL || file == NULL)
    return NULL;

  if (unit->offset_size == 4)
    offset = read_4_bytes (unit->abfd, ptr, buf_end);
  else if (unit->offset_size == 8)
    offset = read_8_bytes (unit->abfd, ptr, buf_end);
  else
    return NULL;

  if (! read_section (unit->abfd, &stash->debug_sections[debug_str],
		      file->syms, offset,
		      &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  if (file->dwarf_str_buffer == NULL)
    return NULL;

  if (offset >= file->dwarf_str_size)
    return NULL;

  str = (char *) file->dwarf_str_buffer + offset;
  if (*str == '\0')
    return NULL;

  return str;
}

/* Like read_indirect_string but from .debug_line_str section.  */

static char *
read_indirect_line_string (struct comp_unit *unit,
                          bfd_byte **ptr,
                          bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  char *str;

  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  stash = unit->stash;
  file = unit->file;

  if (stash == NULL || file == NULL)
    return NULL;

  if (unit->offset_size == 4)
    offset = read_4_bytes (unit->abfd, ptr, buf_end);
  else if (unit->offset_size == 8)
    offset = read_8_bytes (unit->abfd, ptr, buf_end);
  else
    return NULL;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_line_str],
                     file->syms, offset,
                     &file->dwarf_line_str_buffer,
                     &file->dwarf_line_str_size))
    return NULL;

  if (file->dwarf_line_str_buffer == NULL)
    return NULL;

  if (offset >= file->dwarf_line_str_size)
    return NULL;

  str = (char *) file->dwarf_line_str_buffer + offset;
  if (*str == '\0')
    return NULL;

  return str;
}

/* Like read_indirect_string but uses a .debug_str located in
   an alternate file pointed to by the .gnu_debugaltlink section.
   Used to impement DW_FORM_GNU_strp_alt.  */

static char *
read_alt_indirect_string (struct comp_unit *unit,
			  bfd_byte **ptr,
			  bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash = unit->stash;
  char *str;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  if (unit->offset_size == 4)
    offset = read_4_bytes (unit->abfd, ptr, buf_end);
  else
    offset = read_8_bytes (unit->abfd, ptr, buf_end);

  if (stash->alt.bfd_ptr == NULL)
    {
      if (!open_alt_debug_file (unit, stash))
        return NULL;
    }

  if (!read_section (unit->stash->alt.bfd_ptr,
		      stash->debug_sections + debug_str_alt,
		      stash->alt.syms, offset,
		      &stash->alt.dwarf_str_buffer,
		      &stash->alt.dwarf_str_size))
    return NULL;

  if (offset >= stash->alt.dwarf_str_size)
    return NULL;

  str = (char *) stash->alt.dwarf_str_buffer + offset;
  if (*str == '\0')
    return NULL;

  return str;
}

static bool
open_alt_debug_file (struct comp_unit *unit, struct dwarf2_debug *stash)
{
  bfd *debug_bfd;
  char *debug_filename = bfd_follow_gnu_debugaltlink (unit->abfd, DEBUGDIR);

  if (debug_filename == NULL)
    return false;

  debug_bfd = bfd_openr (debug_filename, NULL);
  free (debug_filename);
  
  if (debug_bfd == NULL)
    return false;

  if (!bfd_check_format (debug_bfd, bfd_object))
    {
      bfd_close (debug_bfd);
      return false;
    }
  
  stash->alt.bfd_ptr = debug_bfd;
  return true;
}

/* Resolve an alternate reference from UNIT at OFFSET.
   Returns a pointer into the loaded alternate CU upon success
   or NULL upon failure.  */

static bfd_byte *
read_alt_indirect_ref (struct comp_unit *unit, uint64_t offset)
{
  struct dwarf2_debug *stash = unit->stash;

  if (stash->alt.bfd_ptr == NULL)
    {
      if (!open_alt_debug_file(unit))
        return NULL;
    }

  if (!read_section(unit->stash->alt.bfd_ptr,
                    stash->debug_sections + debug_info_alt,
                    stash->alt.syms, offset,
                    &stash->alt.dwarf_info_buffer,
                    &stash->alt.dwarf_info_size))
    return NULL;

  return stash->alt.dwarf_info_buffer + offset;
}

static bool
open_alt_debug_file(struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;
  char *debug_filename = bfd_follow_gnu_debugaltlink(unit->abfd, DEBUGDIR);

  if (debug_filename == NULL)
    return false;

  bfd *debug_bfd = bfd_openr(debug_filename, NULL);
  free(debug_filename);
  
  if (debug_bfd == NULL)
    return false;

  if (!bfd_check_format(debug_bfd, bfd_object))
    {
      bfd_close(debug_bfd);
      return false;
    }
  
  stash->alt.bfd_ptr = debug_bfd;
  return true;
}

static uint64_t
read_address (struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
  bfd_byte *buf = *ptr;
  int signed_vma = 0;
  uint64_t result = 0;

  if (unit == NULL || ptr == NULL || buf == NULL || buf_end == NULL) {
    return 0;
  }

  if (bfd_get_flavour (unit->abfd) == bfd_target_elf_flavour) {
    signed_vma = get_elf_backend_data (unit->abfd)->sign_extend_vma;
  }

  if (unit->addr_size > (size_t) (buf_end - buf)) {
    *ptr = buf_end;
    return 0;
  }

  *ptr = buf + unit->addr_size;
  
  if (signed_vma) {
    result = read_signed_value(unit, buf);
  } else {
    result = read_unsigned_value(unit, buf);
  }
  
  return result;
}

static uint64_t
read_signed_value(struct comp_unit *unit, bfd_byte *buf)
{
  switch (unit->addr_size) {
    case 8:
      return bfd_get_signed_64 (unit->abfd, buf);
    case 4:
      return bfd_get_signed_32 (unit->abfd, buf);
    case 2:
      return bfd_get_signed_16 (unit->abfd, buf);
    default:
      return 0;
  }
}

static uint64_t
read_unsigned_value(struct comp_unit *unit, bfd_byte *buf)
{
  switch (unit->addr_size) {
    case 8:
      return bfd_get_64 (unit->abfd, buf);
    case 4:
      return bfd_get_32 (unit->abfd, buf);
    case 2:
      return bfd_get_16 (unit->abfd, buf);
    default:
      return 0;
  }
}

/* Lookup an abbrev_info structure in the abbrev hash table.  */

static struct abbrev_info *
lookup_abbrev (unsigned int number, struct abbrev_info **abbrevs)
{
  if (abbrevs == NULL)
    return NULL;

  unsigned int hash_number = number % ABBREV_HASH_SIZE;
  struct abbrev_info *abbrev = abbrevs[hash_number];

  while (abbrev != NULL)
    {
      if (abbrev->number == number)
        return abbrev;
      abbrev = abbrev->next;
    }

  return NULL;
}

/* We keep a hash table to map .debug_abbrev section offsets to the
   array of abbrevs, so that compilation units using the same set of
   abbrevs do not waste memory.  */

struct abbrev_offset_entry
{
  size_t offset;
  struct abbrev_info **abbrevs;
};

static hashval_t
hash_abbrev (const void *p)
{
  if (p == NULL)
    return 0;
  
  const struct abbrev_offset_entry *ent = (const struct abbrev_offset_entry *)p;
  return htab_hash_pointer ((void *)(uintptr_t)ent->offset);
}

static int eq_abbrev(const void *pa, const void *pb)
{
    if (pa == NULL || pb == NULL) {
        return 0;
    }
    
    const struct abbrev_offset_entry *a = pa;
    const struct abbrev_offset_entry *b = pb;
    
    return a->offset == b->offset;
}

static void
del_abbrev (void *p)
{
  if (p == NULL)
    return;

  struct abbrev_offset_entry *ent = p;
  
  if (ent->abbrevs != NULL)
    {
      for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
        {
          struct abbrev_info *abbrev = ent->abbrevs[i];
          while (abbrev != NULL)
            {
              struct abbrev_info *next = abbrev->next;
              if (abbrev->attrs != NULL)
                free (abbrev->attrs);
              free (abbrev);
              abbrev = next;
            }
        }
      free (ent->abbrevs);
    }
  
  free (ent);
}

/* In DWARF version 2, the description of the debugging information is
   stored in a separate .debug_abbrev section.  Before we read any
   dies from a section we read in all abbreviations and install them
   in a hash table.  */

static struct abbrev_info**
read_abbrevs (bfd *abfd, uint64_t offset, struct dwarf2_debug *stash,
	      struct dwarf2_debug_file *file)
{
  struct abbrev_info **abbrevs = NULL;
  struct abbrev_offset_entry ent = { offset, NULL };
  void **slot;

  if (ent.offset != offset)
    return NULL;

  slot = htab_find_slot (file->abbrev_offsets, &ent, INSERT);
  if (slot == NULL)
    return NULL;
  if (*slot != NULL)
    return ((struct abbrev_offset_entry *) (*slot))->abbrevs;

  if (! read_section (abfd, &stash->debug_sections[debug_abbrev],
		      file->syms, offset,
		      &file->dwarf_abbrev_buffer,
		      &file->dwarf_abbrev_size))
    return NULL;

  size_t amt = sizeof (struct abbrev_info*) * ABBREV_HASH_SIZE;
  abbrevs = (struct abbrev_info **) bfd_zalloc (abfd, amt);
  if (abbrevs == NULL)
    return NULL;

  bfd_byte *abbrev_ptr = file->dwarf_abbrev_buffer + offset;
  bfd_byte *abbrev_end = file->dwarf_abbrev_buffer + file->dwarf_abbrev_size;
  
  unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr,
					 false, abbrev_end);

  while (abbrev_number)
    {
      struct abbrev_info *cur_abbrev = process_single_abbrev(abfd, &abbrev_ptr, 
                                                             abbrev_end, abbrev_number);
      if (cur_abbrev == NULL)
        goto fail;

      unsigned int hash_number = abbrev_number % ABBREV_HASH_SIZE;
      cur_abbrev->next = abbrevs[hash_number];
      abbrevs[hash_number] = cur_abbrev;

      if ((size_t) (abbrev_ptr - file->dwarf_abbrev_buffer) >= file->dwarf_abbrev_size)
        break;
        
      abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
      if (lookup_abbrev (abbrev_number, abbrevs) != NULL)
        break;
    }

  if (!store_abbrev_entry(slot, &ent, abbrevs))
    goto fail;
    
  return abbrevs;

 fail:
  cleanup_abbrevs(abbrevs);
  return NULL;
}

static struct abbrev_info* 
process_single_abbrev(bfd *abfd, bfd_byte **abbrev_ptr, bfd_byte *abbrev_end, 
                      unsigned int abbrev_number)
{
  size_t amt = sizeof (struct abbrev_info);
  struct abbrev_info *cur_abbrev = (struct abbrev_info *) bfd_zalloc (abfd, amt);
  if (cur_abbrev == NULL)
    return NULL;

  cur_abbrev->number = abbrev_number;
  cur_abbrev->tag = (enum dwarf_tag)
    _bfd_safe_read_leb128 (abfd, abbrev_ptr, false, abbrev_end);
  cur_abbrev->has_children = read_1_byte (abfd, abbrev_ptr, abbrev_end);

  if (!read_abbrev_attributes(abfd, abbrev_ptr, abbrev_end, cur_abbrev))
    return NULL;
    
  return cur_abbrev;
}

static bool 
read_abbrev_attributes(bfd *abfd, bfd_byte **abbrev_ptr, bfd_byte *abbrev_end,
                       struct abbrev_info *cur_abbrev)
{
  for (;;)
    {
      bfd_vma implicit_const = -1;
      unsigned int abbrev_name = _bfd_safe_read_leb128 (abfd, abbrev_ptr,
                                               false, abbrev_end);
      unsigned int abbrev_form = _bfd_safe_read_leb128 (abfd, abbrev_ptr,
                                               false, abbrev_end);
      
      if (abbrev_form == DW_FORM_implicit_const)
        implicit_const = _bfd_safe_read_leb128 (abfd, abbrev_ptr, true, abbrev_end);
        
      if (abbrev_name == 0)
        break;

      if (!add_attribute(cur_abbrev, abbrev_name, abbrev_form, implicit_const))
        return false;
    }
  return true;
}

static bool 
add_attribute(struct abbrev_info *cur_abbrev, unsigned int abbrev_name,
              unsigned int abbrev_form, bfd_vma implicit_const)
{
  if ((cur_abbrev->num_attrs % ATTR_ALLOC_CHUNK) == 0)
    {
      size_t amt = cur_abbrev->num_attrs + ATTR_ALLOC_CHUNK;
      amt *= sizeof (struct attr_abbrev);
      struct attr_abbrev *tmp = (struct attr_abbrev *) bfd_realloc (cur_abbrev->attrs, amt);
      if (tmp == NULL)
        return false;
      cur_abbrev->attrs = tmp;
    }

  cur_abbrev->attrs[cur_abbrev->num_attrs].name = (enum dwarf_attribute) abbrev_name;
  cur_abbrev->attrs[cur_abbrev->num_attrs].form = (enum dwarf_form) abbrev_form;
  cur_abbrev->attrs[cur_abbrev->num_attrs].implicit_const = implicit_const;
  ++cur_abbrev->num_attrs;
  return true;
}

static bool 
store_abbrev_entry(void **slot, struct abbrev_offset_entry *ent, 
                   struct abbrev_info **abbrevs)
{
  *slot = bfd_malloc (sizeof (*ent));
  if (!*slot)
    return false;
  ent->abbrevs = abbrevs;
  memcpy (*slot, ent, sizeof (*ent));
  return true;
}

static void 
cleanup_abbrevs(struct abbrev_info **abbrevs)
{
  if (abbrevs != NULL)
    {
      for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
        {
          struct abbrev_info *abbrev = abbrevs[i];
          while (abbrev)
            {
              free (abbrev->attrs);
              abbrev = abbrev->next;
            }
        }
      free (abbrevs);
    }
}

/* Returns true if the form is one which has a string value.  */

static bool
is_str_form (const struct attribute *attr)
{
  if (attr == NULL)
    return false;

  switch (attr->form)
    {
    case DW_FORM_string:
    case DW_FORM_strp:
    case DW_FORM_strx:
    case DW_FORM_strx1:
    case DW_FORM_strx2:
    case DW_FORM_strx3:
    case DW_FORM_strx4:
    case DW_FORM_line_strp:
    case DW_FORM_GNU_strp_alt:
      return true;

    default:
      return false;
    }
}

/* Returns true if the form is one which has an integer value.  */

static bool
is_int_form (const struct attribute *attr)
{
  if (attr == NULL) {
    return false;
  }

  switch (attr->form)
    {
    case DW_FORM_addr:
    case DW_FORM_data2:
    case DW_FORM_data4:
    case DW_FORM_data8:
    case DW_FORM_data1:
    case DW_FORM_flag:
    case DW_FORM_sdata:
    case DW_FORM_udata:
    case DW_FORM_ref_addr:
    case DW_FORM_ref1:
    case DW_FORM_ref2:
    case DW_FORM_ref4:
    case DW_FORM_ref8:
    case DW_FORM_ref_udata:
    case DW_FORM_sec_offset:
    case DW_FORM_flag_present:
    case DW_FORM_ref_sig8:
    case DW_FORM_addrx:
    case DW_FORM_implicit_const:
    case DW_FORM_addrx1:
    case DW_FORM_addrx2:
    case DW_FORM_addrx3:
    case DW_FORM_addrx4:
    case DW_FORM_GNU_ref_alt:
      return true;

    default:
      return false;
    }
}

/* Returns true if the form is strx[1-4].  */

static inline bool
is_strx_form (enum dwarf_form form)
{
  switch (form) {
    case DW_FORM_strx:
    case DW_FORM_strx1:
    case DW_FORM_strx2:
    case DW_FORM_strx3:
    case DW_FORM_strx4:
      return true;
    default:
      return false;
  }
}

/* Return true if the form is addrx[1-4].  */

static inline bool
is_addrx_form (enum dwarf_form form)
{
  switch (form)
    {
    case DW_FORM_addrx:
    case DW_FORM_addrx1:
    case DW_FORM_addrx2:
    case DW_FORM_addrx3:
    case DW_FORM_addrx4:
      return true;
    default:
      return false;
    }
}

/* Returns the address in .debug_addr section using DW_AT_addr_base.
   Used to implement DW_FORM_addrx*.  */
static uint64_t
read_indexed_address (uint64_t idx, struct comp_unit *unit)
{
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  bfd_byte *info_ptr;
  size_t offset;

  if (unit == NULL)
    return 0;

  stash = unit->stash;
  file = unit->file;

  if (stash == NULL || file == NULL)
    return 0;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_addr],
                     file->syms, 0,
                     &file->dwarf_addr_buffer, &file->dwarf_addr_size))
    return 0;

  if (_bfd_mul_overflow (idx, unit->addr_size, &offset))
    return 0;

  offset += unit->dwarf_addr_offset;
  if (offset < unit->dwarf_addr_offset)
    return 0;

  if (offset > file->dwarf_addr_size)
    return 0;

  if (file->dwarf_addr_size - offset < unit->addr_size)
    return 0;

  info_ptr = file->dwarf_addr_buffer + offset;

  switch (unit->addr_size)
    {
    case 4:
      return bfd_get_32 (unit->abfd, info_ptr);
    case 8:
      return bfd_get_64 (unit->abfd, info_ptr);
    default:
      return 0;
    }
}

/* Returns the string using DW_AT_str_offsets_base.
   Used to implement DW_FORM_strx*.  */
static const char *
read_indexed_string (uint64_t idx, struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  bfd_byte *info_ptr;
  uint64_t str_offset;
  size_t offset;

  if (stash == NULL)
    return NULL;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_str],
		     file->syms, 0,
		     &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_str_offsets],
		     file->syms, 0,
		     &file->dwarf_str_offsets_buffer,
		     &file->dwarf_str_offsets_size))
    return NULL;

  if (_bfd_mul_overflow (idx, unit->offset_size, &offset))
    return NULL;

  offset += unit->dwarf_str_offset;
  if (offset < unit->dwarf_str_offset
      || offset > file->dwarf_str_offsets_size
      || file->dwarf_str_offsets_size - offset < unit->offset_size)
    return NULL;

  info_ptr = file->dwarf_str_offsets_buffer + offset;

  if (unit->offset_size == 4)
    str_offset = bfd_get_32 (unit->abfd, info_ptr);
  else if (unit->offset_size == 8)
    str_offset = bfd_get_64 (unit->abfd, info_ptr);
  else
    return NULL;

  if (str_offset >= file->dwarf_str_size)
    return NULL;
  return (const char *) file->dwarf_str_buffer + str_offset;
}

/* Read and fill in the value of attribute ATTR as described by FORM.
   Read data starting from INFO_PTR, but never at or beyond INFO_PTR_END.
   Returns an updated INFO_PTR taking into account the amount of data read.  */

static bfd_byte *
read_attribute_value (struct attribute *  attr,
		      unsigned		  form,
		      bfd_vma		  implicit_const,
		      struct comp_unit *  unit,
		      bfd_byte *	  info_ptr,
		      bfd_byte *	  info_ptr_end)
{
  bfd *abfd = unit->abfd;
  size_t amt;

  if (info_ptr >= info_ptr_end && form != DW_FORM_flag_present)
    {
      _bfd_error_handler (_("DWARF error: info pointer extends beyond end of attributes"));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  attr->form = (enum dwarf_form) form;

  switch (form)
    {
    case DW_FORM_flag_present:
      attr->u.val = 1;
      break;
    case DW_FORM_ref_addr:
      if (unit->version >= 3)
	{
	  if (unit->offset_size == 4)
	    attr->u.val = read_4_bytes (unit->abfd, &info_ptr, info_ptr_end);
	  else
	    attr->u.val = read_8_bytes (unit->abfd, &info_ptr, info_ptr_end);
	  break;
	}
      attr->u.val = read_address (unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addr:
      attr->u.val = read_address (unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_GNU_ref_alt:
    case DW_FORM_sec_offset:
      if (unit->offset_size == 4)
	attr->u.val = read_4_bytes (unit->abfd, &info_ptr, info_ptr_end);
      else
	attr->u.val = read_8_bytes (unit->abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_block2:
      amt = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      attr->u.blk = read_blk (abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;
    case DW_FORM_block4:
      amt = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      attr->u.blk = read_blk (abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;
    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_addr_offset != 0)
	attr->u.val = read_indexed_address (attr->u.val, unit);
      break;
    case DW_FORM_data2:
    case DW_FORM_ref2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_addr_offset != 0)
	attr->u.val = read_indexed_address (attr->u.val, unit);
      break;
    case DW_FORM_addrx3:
      attr->u.val = read_3_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_addr_offset != 0)
	attr->u.val = read_indexed_address(attr->u.val, unit);
      break;
    case DW_FORM_ref4:
    case DW_FORM_data4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_addr_offset != 0)
	attr->u.val = read_indexed_address (attr->u.val, unit);
      break;
    case DW_FORM_data8:
    case DW_FORM_ref8:
    case DW_FORM_ref_sig8:
      attr->u.val = read_8_bytes (abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_string:
      attr->u.str = read_string (&info_ptr, info_ptr_end);
      break;
    case DW_FORM_strp:
      attr->u.str = read_indirect_string (unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_line_strp:
      attr->u.str = read_indirect_line_string (unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_GNU_strp_alt:
      attr->u.str = read_alt_indirect_string (unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_strx1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_str_offset != 0)
	attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
      else
	attr->u.str = NULL;
      break;
    case DW_FORM_strx2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_str_offset != 0)
	attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
      else
	attr->u.str = NULL;
      break;
    case DW_FORM_strx3:
      attr->u.val = read_3_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_str_offset != 0)
	attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
      else
	attr->u.str = NULL;
      break;
    case DW_FORM_strx4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      if (unit->dwarf_str_offset != 0)
	attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
      else
	attr->u.str = NULL;
      break;
    case DW_FORM_strx:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr,
					   false, info_ptr_end);
      if (unit->dwarf_str_offset != 0)
	attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
      else
	attr->u.str = NULL;
      break;
    case DW_FORM_exprloc:
    case DW_FORM_block:
      amt = _bfd_safe_read_leb128 (abfd, &info_ptr,
				   false, info_ptr_end);
      attr->u.blk = read_blk (abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;
    case DW_FORM_block1:
      amt = read_1_byte (abfd, &info_ptr, info_ptr_end);
      attr->u.blk = read_blk (abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;
    case DW_FORM_sdata:
      attr->u.sval = _bfd_safe_read_leb128 (abfd, &info_ptr,
					    true, info_ptr_end);
      break;
    case DW_FORM_rnglistx:
    case DW_FORM_loclistx:
    case DW_FORM_ref_udata:
    case DW_FORM_udata:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr,
					   false, info_ptr_end);
      break;
    case DW_FORM_addrx:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr,
					   false, info_ptr_end);
      if (unit->dwarf_addr_offset != 0)
	attr->u.val = read_indexed_address (attr->u.val, unit);
      break;
    case DW_FORM_indirect:
      form = _bfd_safe_read_leb128 (abfd, &info_ptr,
				    false, info_ptr_end);
      if (form == DW_FORM_implicit_const)
	implicit_const = _bfd_safe_read_leb128 (abfd, &info_ptr,
						true, info_ptr_end);
      info_ptr = read_attribute_value (attr, form, implicit_const, unit,
				       info_ptr, info_ptr_end);
      break;
    case DW_FORM_implicit_const:
      attr->form = DW_FORM_sdata;
      attr->u.sval = implicit_const;
      break;
    case DW_FORM_data16:
      attr->u.blk = read_blk (abfd, &info_ptr, info_ptr_end, 16);
      if (attr->u.blk == NULL)
	return NULL;
      break;
    default:
      _bfd_error_handler (_("DWARF error: invalid or unhandled FORM value: %#x"),
			  form);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return info_ptr;
}

/* Read an attribute described by an abbreviated attribute.  */

static bfd_byte *
read_attribute (struct attribute *    attr,
		struct attr_abbrev *  abbrev,
		struct comp_unit *    unit,
		bfd_byte *	      info_ptr,
		bfd_byte *	      info_ptr_end)
{
  if (attr == NULL || abbrev == NULL || unit == NULL || info_ptr == NULL || info_ptr_end == NULL)
    return NULL;
    
  if (info_ptr >= info_ptr_end)
    return NULL;
    
  attr->name = abbrev->name;
  return read_attribute_value (attr, abbrev->form, abbrev->implicit_const,
				unit, info_ptr, info_ptr_end);
}

/* Return mangling style given LANG.  */

static int
mangle_style (int lang)
{
  if (lang == DW_LANG_Ada83 || lang == DW_LANG_Ada95 || 
      lang == DW_LANG_Ada2005 || lang == DW_LANG_Ada2012)
    return DMGL_GNAT;

  if (lang == DW_LANG_C_plus_plus || lang == DW_LANG_C_plus_plus_03 ||
      lang == DW_LANG_C_plus_plus_11 || lang == DW_LANG_C_plus_plus_14 ||
      lang == DW_LANG_C_plus_plus_17 || lang == DW_LANG_C_plus_plus_20 ||
      lang == DW_LANG_C_plus_plus_23)
    return DMGL_GNU_V3;

  if (lang == DW_LANG_Java)
    return DMGL_JAVA;

  if (lang == DW_LANG_D)
    return DMGL_DLANG;

  if (lang == DW_LANG_Rust || lang == DW_LANG_Rust_old)
    return DMGL_RUST;

  if (lang == DW_LANG_C89 || lang == DW_LANG_C ||
      lang == DW_LANG_Cobol74 || lang == DW_LANG_Cobol85 ||
      lang == DW_LANG_Fortran77 || lang == DW_LANG_Fortran18 ||
      lang == DW_LANG_Fortran23 || lang == DW_LANG_Pascal83 ||
      lang == DW_LANG_PLI || lang == DW_LANG_C99 ||
      lang == DW_LANG_UPC || lang == DW_LANG_C11 ||
      lang == DW_LANG_C17 || lang == DW_LANG_C23 ||
      lang == DW_LANG_Mips_Assembler || lang == DW_LANG_Assembly ||
      lang == DW_LANG_Upc || lang == DW_LANG_HP_Basic91 ||
      lang == DW_LANG_HP_IMacro || lang == DW_LANG_HP_Assembler)
    return 0;

  return DMGL_AUTO;
}

/* Source line information table routines.  */

#define FILE_ALLOC_CHUNK 5
#define DIR_ALLOC_CHUNK 5

struct line_info
{
  struct line_info *	prev_line;
  bfd_vma		address;
  char *		filename;
  unsigned int		line;
  unsigned int		column;
  unsigned int		discriminator;
  unsigned char		op_index;
  unsigned char		end_sequence;		/* End of (sequential) code sequence.  */
};

struct fileinfo
{
  char *		name;
  unsigned int		dir;
  unsigned int		time;
  unsigned int		size;
};

struct line_sequence
{
  bfd_vma		low_pc;
  struct line_sequence* prev_sequence;
  struct line_info*	last_line;  /* Largest VMA.  */
  struct line_info**	line_info_lookup;
  bfd_size_type		num_lines;
};

struct line_info_table
{
  bfd *			abfd;
  unsigned int		num_files;
  unsigned int		num_dirs;
  unsigned int		num_sequences;
  bool                  use_dir_and_file_0;
  char *		comp_dir;
  char **		dirs;
  struct fileinfo*	files;
  struct line_sequence* sequences;
  struct line_info*	lcl_head;   /* Local head; used in 'add_line_info'.  */
};

/* Remember some information about each function.  If the function is
   inlined (DW_TAG_inlined_subroutine) it may have two additional
   attributes, DW_AT_call_file and DW_AT_call_line, which specify the
   source code location where this function was inlined.  */

struct funcinfo
{
  /* Pointer to previous function in list of all functions.  */
  struct funcinfo *prev_func;
  /* Pointer to function one scope higher.  */
  struct funcinfo *caller_func;
  /* Source location file name where caller_func inlines this func.  */
  char *caller_file;
  /* Source location file name.  */
  char *file;
  /* Source location line number where caller_func inlines this func.  */
  int caller_line;
  /* Source location line number.  */
  int line;
  int tag;
  bool is_linkage;
  const char *name;
  struct arange arange;
  /* The offset of the funcinfo from the start of the unit.  */
  uint64_t unit_offset;
};

struct lookup_funcinfo
{
  /* Function information corresponding to this lookup table entry.  */
  struct funcinfo *funcinfo;

  /* The lowest address for this specific function.  */
  bfd_vma low_addr;

  /* The highest address of this function before the lookup table is sorted.
     The highest address of all prior functions after the lookup table is
     sorted, which is used for binary search.  */
  bfd_vma high_addr;
  /* Index of this function, used to ensure qsort is stable.  */
  unsigned int idx;
};

struct varinfo
{
  /* Pointer to previous variable in list of all variables.  */
  struct varinfo *prev_var;
  /* The offset of the varinfo from the start of the unit.  */
  uint64_t unit_offset;
  /* Source location file name.  */
  char *file;
  /* Source location line number.  */
  int line;
  /* The type of this variable.  */
  int tag;
  /* The name of the variable, if it has one.  */
  const char *name;
  /* The address of the variable.  */
  bfd_vma addr;
  /* Is this a stack variable?  */
  bool stack;
};

/* Return TRUE if NEW_LINE should sort after LINE.  */

static inline bool
new_line_sorts_after (struct line_info *new_line, struct line_info *line)
{
  if (new_line->address != line->address)
    return new_line->address > line->address;
  return new_line->op_index > line->op_index;
}


/* Adds a new entry to the line_info list in the line_info_table, ensuring
   that the list is sorted.  Note that the line_info list is sorted from
   highest to lowest VMA (with possible duplicates); that is,
   line_info->prev_line always accesses an equal or smaller VMA.  */

static bool
add_line_info (struct line_info_table *table,
	       bfd_vma address,
	       unsigned char op_index,
	       char *filename,
	       unsigned int line,
	       unsigned int column,
	       unsigned int discriminator,
	       int end_sequence)
{
  if (table == NULL)
    return false;

  size_t amt = sizeof (struct line_info);
  struct line_info* info = (struct line_info *) bfd_alloc (table->abfd, amt);
  if (info == NULL)
    return false;

  info->prev_line = NULL;
  info->address = address;
  info->op_index = op_index;
  info->line = line;
  info->column = column;
  info->discriminator = discriminator;
  info->end_sequence = end_sequence;
  info->filename = NULL;

  if (filename && filename[0])
    {
      size_t filename_len = strlen (filename);
      if (filename_len > 0)
        {
          info->filename = (struct char *) bfd_alloc (table->abfd, filename_len + 1);
          if (info->filename == NULL)
            return false;
          memcpy (info->filename, filename, filename_len + 1);
        }
    }

  struct line_sequence* seq = table->sequences;

  if (seq && seq->last_line &&
      seq->last_line->address == address &&
      seq->last_line->op_index == op_index &&
      seq->last_line->end_sequence == end_sequence)
    {
      if (table->lcl_head == seq->last_line)
        table->lcl_head = info;
      info->prev_line = seq->last_line->prev_line;
      seq->last_line = info;
      return true;
    }

  if (!seq || !seq->last_line || seq->last_line->end_sequence)
    {
      amt = sizeof (struct line_sequence);
      seq = (struct line_sequence *) bfd_malloc (amt);
      if (seq == NULL)
        return false;
      seq->low_pc = address;
      seq->prev_sequence = table->sequences;
      seq->last_line = info;
      table->lcl_head = info;
      table->sequences = seq;
      table->num_sequences++;
      return true;
    }

  if (info->end_sequence || new_line_sorts_after (info, seq->last_line))
    {
      info->prev_line = seq->last_line;
      seq->last_line = info;
      if (!table->lcl_head)
        table->lcl_head = info;
      return true;
    }

  if (table->lcl_head && !new_line_sorts_after (info, table->lcl_head))
    {
      if (!table->lcl_head->prev_line ||
          new_line_sorts_after (info, table->lcl_head->prev_line))
        {
          info->prev_line = table->lcl_head->prev_line;
          table->lcl_head->prev_line = info;
          return true;
        }
    }

  struct line_info* li2 = seq->last_line;
  struct line_info* li1 = li2 ? li2->prev_line : NULL;

  while (li1)
    {
      if (!new_line_sorts_after (info, li2) &&
          new_line_sorts_after (info, li1))
        break;
      li2 = li1;
      li1 = li1->prev_line;
    }

  if (li2)
    {
      table->lcl_head = li2;
      info->prev_line = li2->prev_line;
      li2->prev_line = info;
    }

  if (address < seq->low_pc)
    seq->low_pc = address;

  return true;
}

/* Extract a fully qualified filename from a line info table.
   The returned string has been malloc'ed and it is the caller's
   responsibility to free it.  */

static char *
concat_filename (struct line_info_table *table, unsigned int file)
{
  char *filename;
  char *dir_name = NULL;
  char *subdir_name = NULL;
  char *result;
  size_t len;
  unsigned int dir;
  unsigned int adjusted_file = file;

  if (table == NULL)
    {
      _bfd_error_handler
        (_("DWARF error: mangled line number section (bad file number)"));
      return strdup ("<unknown>");
    }

  if (!table->use_dir_and_file_0)
    {
      if (file == 0)
        return strdup ("<unknown>");
      adjusted_file = file - 1;
    }

  if (adjusted_file >= table->num_files)
    {
      _bfd_error_handler
        (_("DWARF error: mangled line number section (bad file number)"));
      return strdup ("<unknown>");
    }

  filename = table->files[adjusted_file].name;
  if (filename == NULL)
    return strdup ("<unknown>");

  if (IS_ABSOLUTE_PATH (filename))
    return strdup (filename);

  dir = table->files[adjusted_file].dir;
  if (!table->use_dir_and_file_0 && dir > 0)
    dir--;

  if (dir < table->num_dirs)
    subdir_name = table->dirs[dir];

  if (subdir_name == NULL || !IS_ABSOLUTE_PATH (subdir_name))
    dir_name = table->comp_dir;

  if (dir_name == NULL)
    {
      dir_name = subdir_name;
      subdir_name = NULL;
    }

  if (dir_name == NULL)
    return strdup (filename);

  len = strlen (dir_name) + strlen (filename) + 2;
  if (subdir_name != NULL)
    len += strlen (subdir_name) + 1;

  result = (char *) bfd_malloc (len);
  if (result == NULL)
    return NULL;

  if (subdir_name != NULL)
    snprintf (result, len, "%s/%s/%s", dir_name, subdir_name, filename);
  else
    snprintf (result, len, "%s/%s", dir_name, filename);

  return result;
}

/* Number of bits in a bfd_vma.  */
#define VMA_BITS (8 * sizeof (bfd_vma))

/* Check whether [low1, high1) can be combined with [low2, high2),
   i.e., they touch or overlap.  */

static bool
ranges_overlap (bfd_vma low1,
		bfd_vma high1,
		bfd_vma low2,
		bfd_vma high2)
{
  if (low1 == low2 || high1 == high2)
    return true;

  if (low1 > low2)
    {
      bfd_vma temp_low = low1;
      bfd_vma temp_high = high1;
      low1 = low2;
      high1 = high2;
      low2 = temp_low;
      high2 = temp_high;
    }

  return low2 <= high1;
}

/* Insert an address range in the trie mapping addresses to compilation units.
   Will return the new trie node (usually the same as is being sent in, but
   in case of a leaf-to-interior conversion, or expansion of a leaf, it may be
   different), or NULL on failure.  */

static struct trie_node *
insert_arange_in_trie (bfd *abfd,
		       struct trie_node *trie,
		       bfd_vma trie_pc,
		       unsigned int trie_pc_bits,
		       struct comp_unit *unit,
		       bfd_vma low_pc,
		       bfd_vma high_pc)
{
  if (!trie || !abfd || !unit)
    return NULL;

  if (trie->num_room_in_leaf > 0)
    {
      struct trie_leaf *leaf = (struct trie_leaf *) trie;
      
      for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
	{
	  if (leaf->ranges[i].unit == unit
	      && ranges_overlap (low_pc, high_pc,
				 leaf->ranges[i].low_pc,
				 leaf->ranges[i].high_pc))
	    {
	      if (low_pc < leaf->ranges[i].low_pc)
		leaf->ranges[i].low_pc = low_pc;
	      if (high_pc > leaf->ranges[i].high_pc)
		leaf->ranges[i].high_pc = high_pc;
	      return trie;
	    }
	}

      if (leaf->num_stored_in_leaf == trie->num_room_in_leaf)
	{
	  if (trie_pc_bits < VMA_BITS)
	    {
	      bfd_vma bucket_high_pc = trie_pc + ((bfd_vma) -1 >> trie_pc_bits);
	      bool can_split = false;
	      
	      for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
		{
		  if (leaf->ranges[i].low_pc > trie_pc
		      || leaf->ranges[i].high_pc <= bucket_high_pc)
		    {
		      can_split = true;
		      break;
		    }
		}
	      
	      if (can_split)
		{
		  struct trie_interior *interior = bfd_zalloc (abfd, sizeof (struct trie_interior));
		  if (!interior)
		    return NULL;
		  
		  for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
		    {
		      if (!insert_arange_in_trie (abfd, &interior->head, trie_pc, trie_pc_bits,
						  leaf->ranges[i].unit, leaf->ranges[i].low_pc,
						  leaf->ranges[i].high_pc))
			return NULL;
		    }
		  
		  trie = &interior->head;
		}
	      else
		{
		  trie = resize_leaf (abfd, leaf);
		  if (!trie)
		    return NULL;
		}
	    }
	  else
	    {
	      trie = resize_leaf (abfd, leaf);
	      if (!trie)
		return NULL;
	    }
	}
    }

  if (trie->num_room_in_leaf > 0)
    {
      struct trie_leaf *leaf = (struct trie_leaf *) trie;
      unsigned int i = leaf->num_stored_in_leaf++;
      leaf->ranges[i].unit = unit;
      leaf->ranges[i].low_pc = low_pc;
      leaf->ranges[i].high_pc = high_pc;
      return trie;
    }

  bfd_vma clamped_low_pc = low_pc;
  bfd_vma clamped_high_pc = high_pc;
  
  if (trie_pc_bits > 0)
    {
      bfd_vma bucket_high_pc = trie_pc + ((bfd_vma) -1 >> trie_pc_bits);
      if (clamped_low_pc < trie_pc)
	clamped_low_pc = trie_pc;
      if (clamped_high_pc > bucket_high_pc)
	clamped_high_pc = bucket_high_pc;
    }

  int from_ch = (clamped_low_pc >> (VMA_BITS - trie_pc_bits - 8)) & 0xff;
  int to_ch = ((clamped_high_pc - 1) >> (VMA_BITS - trie_pc_bits - 8)) & 0xff;
  
  for (int ch = from_ch; ch <= to_ch; ++ch)
    {
      struct trie_interior *interior = (struct trie_interior *) trie;
      struct trie_node *child = interior->children[ch];

      if (!child)
        {
	  child = alloc_trie_leaf (abfd);
	  if (!child)
	    return NULL;
	}
      
      bfd_vma bucket = (bfd_vma) ch << (VMA_BITS - trie_pc_bits - 8);
      child = insert_arange_in_trie (abfd, child, trie_pc + bucket,
				     trie_pc_bits + 8, unit, low_pc, high_pc);
      if (!child)
	return NULL;

      interior->children[ch] = child;
    }

  return trie;
}

static struct trie_node *
resize_leaf (bfd *abfd, const struct trie_leaf *leaf)
{
  unsigned int new_room_in_leaf = leaf->head.num_room_in_leaf * 2;
  size_t amt = sizeof (struct trie_leaf) + new_room_in_leaf * sizeof (leaf->ranges[0]);
  struct trie_leaf *new_leaf = bfd_zalloc (abfd, amt);
  
  if (!new_leaf)
    return NULL;
  
  new_leaf->head.num_room_in_leaf = new_room_in_leaf;
  new_leaf->num_stored_in_leaf = leaf->num_stored_in_leaf;
  memcpy (new_leaf->ranges, leaf->ranges,
	  leaf->num_stored_in_leaf * sizeof (leaf->ranges[0]));
  
  return &new_leaf->head;
}

static bool
arange_add (struct comp_unit *unit, struct arange *first_arange,
	    struct trie_node **trie_root, bfd_vma low_pc, bfd_vma high_pc)
{
  struct arange *arange;

  if (low_pc == high_pc)
    return true;

  if (trie_root != NULL)
    {
      *trie_root = insert_arange_in_trie (unit->file->bfd_ptr,
					  *trie_root,
					  0,
					  0,
					  unit,
					  low_pc,
					  high_pc);
      if (*trie_root == NULL)
	return false;
    }

  if (first_arange->high == 0)
    {
      first_arange->low = low_pc;
      first_arange->high = high_pc;
      return true;
    }

  arange = first_arange;
  do
    {
      if (low_pc == arange->high)
	{
	  arange->high = high_pc;
	  return true;
	}
      if (high_pc == arange->low)
	{
	  arange->low = low_pc;
	  return true;
	}
      arange = arange->next;
    }
  while (arange);

  arange = (struct arange *) bfd_alloc (unit->abfd, sizeof (*arange));
  if (arange == NULL)
    return false;
  arange->low = low_pc;
  arange->high = high_pc;
  arange->next = first_arange->next;
  first_arange->next = arange;
  return true;
}

/* Compare function for line sequences.  */

static int
compare_sequences (const void* a, const void* b)
{
  const struct line_sequence* seq1 = a;
  const struct line_sequence* seq2 = b;

  if (seq1->low_pc != seq2->low_pc)
    return (seq1->low_pc < seq2->low_pc) ? -1 : 1;

  if (seq1->last_line->address != seq2->last_line->address)
    return (seq1->last_line->address < seq2->last_line->address) ? 1 : -1;

  if (seq1->last_line->op_index != seq2->last_line->op_index)
    return (seq1->last_line->op_index < seq2->last_line->op_index) ? 1 : -1;

  if (seq1->num_lines != seq2->num_lines)
    return (seq1->num_lines < seq2->num_lines) ? -1 : 1;

  return 0;
}

/* Construct the line information table for quick lookup.  */

static bool
build_line_info_table (struct line_info_table *  table,
		       struct line_sequence *    seq)
{
  struct line_info **line_info_lookup;
  struct line_info *each_line;
  unsigned int num_lines;
  unsigned int line_index;

  if (seq->line_info_lookup != NULL)
    return true;

  num_lines = 0;
  for (each_line = seq->last_line; each_line != NULL; each_line = each_line->prev_line)
    num_lines++;

  seq->num_lines = num_lines;
  if (num_lines == 0)
    return true;

  line_info_lookup = (struct line_info**) bfd_alloc (table->abfd, 
                                                      sizeof (struct line_info*) * num_lines);
  if (line_info_lookup == NULL)
    return false;
    
  seq->line_info_lookup = line_info_lookup;

  line_index = num_lines;
  for (each_line = seq->last_line; each_line != NULL; each_line = each_line->prev_line)
    {
      if (line_index == 0)
        return false;
      line_info_lookup[--line_index] = each_line;
    }

  if (line_index != 0)
    return false;
    
  return true;
}

/* Sort the line sequences for quick lookup.  */

static bool
sort_line_sequences (struct line_info_table* table)
{
  if (table->num_sequences == 0)
    return true;

  size_t amt = sizeof (struct line_sequence) * table->num_sequences;
  struct line_sequence *sequences = (struct line_sequence *) bfd_alloc (table->abfd, amt);
  if (sequences == NULL)
    return false;

  struct line_sequence *seq = table->sequences;
  unsigned int n;
  for (n = 0; n < table->num_sequences && seq != NULL; n++)
    {
      sequences[n].low_pc = seq->low_pc;
      sequences[n].prev_sequence = NULL;
      sequences[n].last_line = seq->last_line;
      sequences[n].line_info_lookup = NULL;
      sequences[n].num_lines = n;
      
      struct line_sequence* temp = seq;
      seq = seq->prev_sequence;
      free (temp);
    }

  if (n != table->num_sequences || seq != NULL)
    {
      while (seq != NULL)
        {
          struct line_sequence* temp = seq;
          seq = seq->prev_sequence;
          free (temp);
        }
      return false;
    }

  qsort (sequences, n, sizeof (struct line_sequence), compare_sequences);

  unsigned int num_sequences = 1;
  bfd_vma last_high_pc = sequences[0].last_line->address;
  
  for (n = 1; n < table->num_sequences; n++)
    {
      if (sequences[n].low_pc >= last_high_pc)
        {
          last_high_pc = sequences[n].last_line->address;
          if (n != num_sequences)
            {
              sequences[num_sequences].low_pc = sequences[n].low_pc;
              sequences[num_sequences].last_line = sequences[n].last_line;
            }
          num_sequences++;
        }
      else if (sequences[n].last_line->address > last_high_pc)
        {
          sequences[num_sequences].low_pc = last_high_pc;
          sequences[num_sequences].last_line = sequences[n].last_line;
          last_high_pc = sequences[n].last_line->address;
          num_sequences++;
        }
    }

  table->sequences = sequences;
  table->num_sequences = num_sequences;
  return true;
}

/* Add directory to TABLE.  CUR_DIR memory ownership is taken by TABLE.  */

static bool
line_info_add_include_dir (struct line_info_table *table, char *cur_dir)
{
  if (table == NULL || cur_dir == NULL)
    return false;

  if ((table->num_dirs % DIR_ALLOC_CHUNK) == 0)
    {
      size_t new_capacity = table->num_dirs + DIR_ALLOC_CHUNK;
      size_t amt = new_capacity * sizeof (char *);

      char **tmp = (char **) bfd_realloc (table->dirs, amt);
      if (tmp == NULL)
        return false;
      table->dirs = tmp;
    }

  table->dirs[table->num_dirs] = cur_dir;
  table->num_dirs++;
  return true;
}

static bool
line_info_add_include_dir_stub (struct line_info_table *table, char *cur_dir,
				unsigned int dir ATTRIBUTE_UNUSED,
				unsigned int xtime ATTRIBUTE_UNUSED,
				unsigned int size ATTRIBUTE_UNUSED)
{
  if (table == NULL || cur_dir == NULL)
    return false;
    
  return line_info_add_include_dir (table, cur_dir);
}

/* Add file to TABLE.  CUR_FILE memory ownership is taken by TABLE.  */

static bool
line_info_add_file_name (struct line_info_table *table, char *cur_file,
			 unsigned int dir, unsigned int xtime,
			 unsigned int size)
{
  if (table == NULL || cur_file == NULL)
    return false;

  if ((table->num_files % FILE_ALLOC_CHUNK) == 0)
    {
      size_t new_count = table->num_files + FILE_ALLOC_CHUNK;
      size_t amt = new_count * sizeof (struct fileinfo);
      
      if (new_count < table->num_files)
        return false;
      
      if (amt / sizeof (struct fileinfo) != new_count)
        return false;

      struct fileinfo *tmp = (struct fileinfo *) bfd_realloc (table->files, amt);
      if (tmp == NULL)
        return false;
      table->files = tmp;
    }

  struct fileinfo *new_file = &table->files[table->num_files];
  new_file->name = cur_file;
  new_file->dir = dir;
  new_file->time = xtime;
  new_file->size = size;
  
  table->num_files++;
  return true;
}

/* Read directory or file name entry format, starting with byte of
   format count entries, ULEB128 pairs of entry formats, ULEB128 of
   entries count and the entries themselves in the described entry
   format.  */

static bool
read_formatted_entries (struct comp_unit *unit, bfd_byte **bufp,
			bfd_byte *buf_end, struct line_info_table *table,
			bool (*callback) (struct line_info_table *table,
					  char *cur_file,
					  unsigned int dir,
					  unsigned int time,
					  unsigned int size))
{
  bfd *abfd = unit->abfd;
  bfd_byte format_count, formati;
  bfd_vma data_count, datai;
  bfd_byte *buf = *bufp;
  bfd_byte *format_header_data;

  format_count = read_1_byte (abfd, &buf, buf_end);
  format_header_data = buf;
  
  for (formati = 0; formati < format_count; formati++)
    {
      _bfd_safe_read_leb128 (abfd, &buf, false, buf_end);
      _bfd_safe_read_leb128 (abfd, &buf, false, buf_end);
    }

  data_count = _bfd_safe_read_leb128 (abfd, &buf, false, buf_end);
  
  if (format_count == 0 && data_count != 0)
    {
      _bfd_error_handler (_("DWARF error: zero format count"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (data_count > (bfd_vma) (buf_end - buf))
    {
      _bfd_error_handler
	(_("DWARF error: data count (%" PRIx64 ") larger than buffer size"),
	 (uint64_t) data_count);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  for (datai = 0; datai < data_count; datai++)
    {
      if (!process_single_entry(abfd, unit, table, callback, 
                                &buf, buf_end, format_header_data, format_count))
        return false;
    }

  *bufp = buf;
  return true;
}

static bool
process_single_entry(bfd *abfd, struct comp_unit *unit, 
                     struct line_info_table *table,
                     bool (*callback) (struct line_info_table *table,
                                      char *cur_file,
                                      unsigned int dir,
                                      unsigned int time,
                                      unsigned int size),
                     bfd_byte **buf, bfd_byte *buf_end,
                     bfd_byte *format_header_data, bfd_byte format_count)
{
  bfd_byte *format = format_header_data;
  struct fileinfo fe;
  bfd_byte formati;

  memset (&fe, 0, sizeof fe);
  
  for (formati = 0; formati < format_count; formati++)
    {
      if (!process_format_entry(abfd, unit, &format, buf, buf_end, &fe))
        return false;
    }

  return callback (table, fe.name, fe.dir, fe.time, fe.size);
}

static bool
process_format_entry(bfd *abfd, struct comp_unit *unit,
                    bfd_byte **format, bfd_byte **buf, bfd_byte *buf_end,
                    struct fileinfo *fe)
{
  bfd_vma content_type, form;
  char *string_trash;
  char **stringp = &string_trash;
  unsigned int uint_trash, *uintp = &uint_trash;
  struct attribute attr;

  content_type = _bfd_safe_read_leb128 (abfd, format, false, buf_end);
  
  switch (content_type)
    {
    case DW_LNCT_path:
      stringp = &fe->name;
      break;
    case DW_LNCT_directory_index:
      uintp = &fe->dir;
      break;
    case DW_LNCT_timestamp:
      uintp = &fe->time;
      break;
    case DW_LNCT_size:
      uintp = &fe->size;
      break;
    case DW_LNCT_MD5:
      break;
    default:
      _bfd_error_handler
        (_("DWARF error: unknown format content type %" PRIu64),
         (uint64_t) content_type);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  form = _bfd_safe_read_leb128 (abfd, format, false, buf_end);
  *buf = read_attribute_value (&attr, form, 0, unit, *buf, buf_end);
  
  if (*buf == NULL)
    return false;
    
  assign_attribute_value(form, &attr, stringp, uintp);
  return true;
}

static void
assign_attribute_value(bfd_vma form, struct attribute *attr,
                      char **stringp, unsigned int *uintp)
{
  switch (form)
    {
    case DW_FORM_string:
    case DW_FORM_line_strp:
    case DW_FORM_strx:
    case DW_FORM_strx1:
    case DW_FORM_strx2:
    case DW_FORM_strx3:
    case DW_FORM_strx4:
      *stringp = attr->u.str;
      break;

    case DW_FORM_data1:
    case DW_FORM_data2:
    case DW_FORM_data4:
    case DW_FORM_data8:
    case DW_FORM_udata:
      *uintp = attr->u.val;
      break;

    case DW_FORM_data16:
      break;
    }
}

/* Decode the line number information for UNIT.  */

static struct line_info_table*
decode_line_info (struct comp_unit *unit)
{
  bfd *abfd = unit->abfd;
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  struct line_info_table* table;
  bfd_byte *line_ptr;
  bfd_byte *line_end;
  struct line_head lh;
  unsigned int i, offset_size;
  char *cur_file, *cur_dir;
  unsigned char op_code, extended_op, adj_opcode;
  unsigned int exop_len;
  size_t amt;

  if (unit->line_offset == 0 && file->line_table)
    return file->line_table;

  if (! read_section (abfd, &stash->debug_sections[debug_line],
		      file->syms, unit->line_offset,
		      &file->dwarf_line_buffer, &file->dwarf_line_size))
    return NULL;

  if (file->dwarf_line_size < 16)
    {
      _bfd_error_handler
	(_("DWARF error: line info section is too small (%" PRId64 ")"),
	 (int64_t) file->dwarf_line_size);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  line_ptr = file->dwarf_line_buffer + unit->line_offset;
  line_end = file->dwarf_line_buffer + file->dwarf_line_size;

  if (!read_line_header(abfd, &line_ptr, line_end, &lh, &offset_size, unit))
    return NULL;

  line_end = line_ptr + lh.total_length;

  if (!validate_line_header(abfd, &line_ptr, line_end, &lh, offset_size))
    return NULL;

  amt = lh.opcode_base * sizeof (unsigned char);
  lh.standard_opcode_lengths = (unsigned char *) bfd_alloc (abfd, amt);
  if (!lh.standard_opcode_lengths)
    return NULL;

  lh.standard_opcode_lengths[0] = 1;

  for (i = 1; i < lh.opcode_base; ++i)
    lh.standard_opcode_lengths[i] = read_1_byte (abfd, &line_ptr, line_end);

  amt = sizeof (struct line_info_table);
  table = (struct line_info_table *) bfd_alloc (abfd, amt);
  if (table == NULL)
    return NULL;
  
  initialize_line_table(table, abfd, unit);

  if (!read_file_and_dir_tables(unit, &line_ptr, line_end, table, &lh))
    goto fail;

  if (!process_line_sequences(unit, &line_ptr, line_end, table, &lh))
    goto fail;

  if (unit->line_offset == 0)
    file->line_table = table;
  if (sort_line_sequences (table))
    return table;

 fail:
  cleanup_line_table(table);
  return NULL;
}

static bool read_line_header(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                              struct line_head *lh, unsigned int *offset_size,
                              struct comp_unit *unit)
{
  lh->total_length = read_4_bytes (abfd, line_ptr, line_end);
  *offset_size = 4;
  if (lh->total_length == 0xffffffff)
    {
      lh->total_length = read_8_bytes (abfd, line_ptr, line_end);
      *offset_size = 8;
    }
  else if (lh->total_length == 0 && unit->addr_size == 8)
    {
      lh->total_length = read_4_bytes (abfd, line_ptr, line_end);
      *offset_size = 8;
    }

  if (lh->total_length > (size_t) (line_end - *line_ptr))
    {
      _bfd_error_handler
	(_("DWARF error: line info data is bigger (%#" PRIx64 ")"
	   " than the space remaining in the section (%#lx)"),
	 (uint64_t) lh->total_length, (unsigned long) (line_end - *line_ptr));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool validate_line_header(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                  struct line_head *lh, unsigned int offset_size)
{
  lh->version = read_2_bytes (abfd, line_ptr, line_end);
  if (lh->version < 2 || lh->version > 5)
    {
      _bfd_error_handler
	(_("DWARF error: unhandled .debug_line version %d"), lh->version);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  unsigned int min_header_size = offset_size + (lh->version >= 5 ? 8 : (lh->version >= 4 ? 6 : 5));
  if (*line_ptr + min_header_size >= line_end)
    {
      _bfd_error_handler
	(_("DWARF error: ran out of room reading prologue"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (lh->version >= 5)
    {
      read_1_byte (abfd, line_ptr, line_end);
      unsigned int segment_selector_size = read_1_byte (abfd, line_ptr, line_end);
      if (segment_selector_size != 0)
	{
	  _bfd_error_handler
	    (_("DWARF error: line info unsupported segment selector size %u"),
	     segment_selector_size);
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
    }

  if (offset_size == 4)
    lh->prologue_length = read_4_bytes (abfd, line_ptr, line_end);
  else
    lh->prologue_length = read_8_bytes (abfd, line_ptr, line_end);

  lh->minimum_instruction_length = read_1_byte (abfd, line_ptr, line_end);

  if (lh->version >= 4)
    lh->maximum_ops_per_insn = read_1_byte (abfd, line_ptr, line_end);
  else
    lh->maximum_ops_per_insn = 1;

  if (lh->maximum_ops_per_insn == 0)
    {
      _bfd_error_handler
	(_("DWARF error: invalid maximum operations per instruction"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  lh->default_is_stmt = read_1_byte (abfd, line_ptr, line_end);
  lh->line_base = read_1_signed_byte (abfd, line_ptr, line_end);
  lh->line_range = read_1_byte (abfd, line_ptr, line_end);
  lh->opcode_base = read_1_byte (abfd, line_ptr, line_end);

  if (*line_ptr + (lh->opcode_base - 1) >= line_end)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading opcodes"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static void initialize_line_table(struct line_info_table *table, bfd *abfd, 
                                   struct comp_unit *unit)
{
  table->abfd = abfd;
  table->comp_dir = unit->comp_dir;
  table->num_files = 0;
  table->files = NULL;
  table->num_dirs = 0;
  table->dirs = NULL;
  table->num_sequences = 0;
  table->sequences = NULL;
  table->lcl_head = NULL;
}

static bool read_file_and_dir_tables(struct comp_unit *unit, bfd_byte **line_ptr,
                                      bfd_byte *line_end, struct line_info_table *table,
                                      struct line_head *lh)
{
  if (lh->version >= 5)
    {
      if (!read_formatted_entries (unit, line_ptr, line_end, table,
				   line_info_add_include_dir_stub))
	return false;

      if (!read_formatted_entries (unit, line_ptr, line_end, table,
				   line_info_add_file_name))
	return false;
      table->use_dir_and_file_0 = true;
    }
  else
    {
      char *cur_dir;
      while ((cur_dir = read_string (line_ptr, line_end)) != NULL)
	{
	  if (!line_info_add_include_dir (table, cur_dir))
	    return false;
	}

      char *cur_file;
      while ((cur_file = read_string (line_ptr, line_end)) != NULL)
	{
	  unsigned int dir = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
	  unsigned int xtime = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
	  unsigned int size = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);

	  if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
	    return false;
	}
      table->use_dir_and_file_0 = false;
    }
  return true;
}

static bool process_line_sequences(struct comp_unit *unit, bfd_byte **line_ptr,
                                    bfd_byte *line_end, struct line_info_table *table,
                                    struct line_head *lh)
{
  while (*line_ptr < line_end)
    {
      if (!process_single_sequence(unit, line_ptr, line_end, table, lh))
        return false;
    }
  return true;
}

static bool process_single_sequence(struct comp_unit *unit, bfd_byte **line_ptr,
                                     bfd_byte *line_end, struct line_info_table *table,
                                     struct line_head *lh)
{
  struct line_state state = {0};
  state.line = 1;
  state.is_stmt = lh->default_is_stmt;
  state.low_pc = (bfd_vma) -1;
  
  if (table->num_files)
    state.filename = concat_filename (table, 1);

  while (!state.end_sequence && *line_ptr < line_end)
    {
      if (!process_line_opcode(unit, line_ptr, line_end, table, lh, &state))
        {
          free(state.filename);
          return false;
        }
    }

  free(state.filename);
  return true;
}

static bool process_line_opcode(struct comp_unit *unit, bfd_byte **line_ptr,
                                 bfd_byte *line_end, struct line_info_table *table,
                                 struct line_head *lh, struct line_state *state)
{
  unsigned char op_code = read_1_byte (unit->abfd, line_ptr, line_end);

  if (op_code >= lh->opcode_base)
    return process_special_opcode(unit->abfd, table, lh, state, op_code);
  
  return process_standard_opcode(unit, line_ptr, line_end, table, lh, state, op_code);
}

static bool process_special_opcode(bfd *abfd, struct line_info_table *table,
                                    struct line_head *lh, struct line_state *state,
                                    unsigned char op_code)
{
  if (lh->line_range == 0)
    return false;

  unsigned char adj_opcode = op_code - lh->opcode_base;
  
  if (lh->maximum_ops_per_insn == 1)
    {
      state->address += (adj_opcode / lh->line_range * lh->minimum_instruction_length);
    }
  else
    {
      state->address += ((state->op_index + adj_opcode / lh->line_range)
                         / lh->maximum_ops_per_insn * lh->minimum_instruction_length);
      state->op_index = ((state->op_index + adj_opcode / lh->line_range)
                         % lh->maximum_ops_per_insn);
    }

  state->line += lh->line_base + (adj_opcode % lh->line_range);
  
  if (!add_line_info (table, state->address, state->op_index, state->filename,
                      state->line, state->column, state->discriminator, 0))
    return false;

  state->discriminator = 0;
  update_pc_bounds(state);
  return true;
}

static bool process_standard_opcode(struct comp_unit *unit, bfd_byte **line_ptr,
                                     bfd_byte *line_end, struct line_info_table *table,
                                     struct line_head *lh, struct line_state *state,
                                     unsigned char op_code)
{
  switch (op_code)
    {
    case DW_LNS_extended_op:
      return process_extended_opcode(unit, line_ptr, line_end, table, state);
      
    case DW_LNS_copy:
      if (!add_line_info (table, state->address, state->op_index,
                          state->filename, state->line, state->column, 
                          state->discriminator, 0))
        return false;
      state->discriminator = 0;
      update_pc_bounds(state);
      break;
      
    case DW_LNS_advance_pc:
      advance_pc(unit->abfd, line_ptr, line_end, lh, state);
      break;
      
    case DW_LNS_advance_line:
      state->line += _bfd_safe_read_leb128 (unit->abfd, line_ptr, true, line_end);
      break;
      
    case DW_LNS_set_file:
      {
        unsigned int filenum = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
        free (state->filename);
        state->filename = concat_filename (table, filenum);
      }
      break;
      
    case DW_LNS_set_column:
      state->column = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
      break;
      
    case DW_LNS_negate_stmt:
      state->is_stmt = !state->is_stmt;
      break;
      
    case DW_LNS_set_basic_block:
      break;
      
    case DW_LNS_const_add_pc:
      const_add_pc(lh, state);
      break;
      
    case DW_LNS_fixed_advance_pc:
      state->address += read_2_bytes (unit->abfd, line_ptr, line_end);
      state->op_index = 0;
      break;
      
    default:
      skip_unknown_opcode(unit->abfd, line_ptr, line_end, lh, op_code);
      break;
    }
  return true;
}

static bool process_extended_opcode(struct comp_unit *unit, bfd_byte **line_ptr,
                                     bfd_byte *line_end, struct line_info_table *table,
                                     struct line_state *state)
{
  unsigned int exop_len = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
  unsigned char extended_op = read_1_byte (unit->abfd, line_ptr, line_end);

  switch (extended_op)
    {
    case DW_LNE_end_sequence:
      state->end_sequence = 1;
      if (!add_line_info (table, state->address, state->op_index, state->filename,
                          state->line, state->column, state->discriminator, 
                          state->end_sequence))
        return false;
      state->discriminator = 0;
      update_pc_bounds(state);
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
                       state->low_pc, state->high_pc))
        return false;
      break;
      
    case DW_LNE_set_address:
      state->address = read_address (unit, line_ptr, line_end);
      state->op_index = 0;
      break;
      
    case DW_LNE_define_file:
      {
        char *cur_file = read_string (line_ptr, line_end);
        unsigned int dir = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
        unsigned int xtime = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
        unsigned int size = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
        if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
          return false;
      }
      break;
      
    case DW_LNE_set_discriminator:
      state->discriminator = _bfd_safe_read_leb128 (unit->abfd, line_ptr, false, line_end);
      break;
      
    case DW_LNE_HP_source_file_correlation:
      *line_ptr += exop_len - 1;
      break;
      
    default:
      _bfd_error_handler (_("DWARF error: mangled line number section"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static void advance_pc(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                       struct line_head *lh, struct line_state *state)
{
  bfd_vma adjust = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
  
  if (lh->maximum_ops_per_insn == 1)
    {
      state->address += lh->minimum_instruction_length * adjust;
    }
  else
    {
      state->address = ((state->op_index + adjust) / lh->maximum_ops_per_insn
                        * lh->minimum_instruction_length);
      state->op_index = (state->op_index + adjust) % lh->maximum_ops_per_insn;
    }
}

static void const_add_pc(struct line_head *lh, struct line_state *state)
{
  if (lh->line_range == 0)
    return;
    
  if (lh->maximum_ops_per_insn == 1)
    {
      state->address += (lh->minimum_instruction_length
                         * ((255 - lh->opcode_base) / lh->line_range));
    }
  else
    {
      bfd_vma adjust = ((255 - lh->opcode_base) / lh->line_range);
      state->address += (lh->minimum_instruction_length
                         * ((state->op_index + adjust) / lh->maximum_ops_per_insn));
      state->op_index = (state->op_index + adjust) % lh->maximum_ops_per_insn;
    }
}

static void skip_unknown_opcode(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                 struct line_head *lh, unsigned char op_code)
{
  for (unsigned int i = 0; i < lh->standard_opcode_lengths[op_code]; i++)
    (void) _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
}

static void update_pc_bounds(struct line_state *state)
{
  if (state->address < state->low_pc)
    state->low_pc = state->address;
  if (state->address > state->high_pc)
    state->high_pc = state->address;
}

static void cleanup_line_table(struct line_info_table *table)
{
  while (table->sequences != NULL)
    {
      struct line_sequence* seq = table->sequences;
      table->sequences = table->sequences->prev_sequence;
      free (seq);
    }
  free (table->files);
  free (table->dirs);
}

struct line_state {
  bfd_vma address;
  unsigned char op_index;
  char *filename;
  unsigned int line;
  unsigned int column;
  unsigned int discriminator;
  int is_stmt;
  int end_sequence;
  bfd_vma low_pc;
  bfd_vma high_pc;
};

/* If ADDR is within TABLE set the output parameters and return TRUE,
   otherwise set *FILENAME_PTR to NULL and return FALSE.
   The parameters FILENAME_PTR, LINENUMBER_PTR and DISCRIMINATOR_PTR
   are pointers to the objects to be filled in.  */

static bool
lookup_address_in_line_info_table (struct line_info_table *table,
				   bfd_vma addr,
				   const char **filename_ptr,
				   unsigned int *linenumber_ptr,
				   unsigned int *discriminator_ptr)
{
  struct line_sequence *seq = NULL;
  struct line_info *info = NULL;
  int low, high, mid;

  if (!table || !filename_ptr || !linenumber_ptr) {
    if (filename_ptr)
      *filename_ptr = NULL;
    return false;
  }

  low = 0;
  high = table->num_sequences;
  while (low < high)
    {
      mid = (low + high) / 2;
      seq = &table->sequences[mid];
      if (addr < seq->low_pc)
	high = mid;
      else if (addr >= seq->last_line->address)
	low = mid + 1;
      else
	break;
    }

  if (low >= high || !seq || addr < seq->low_pc || addr >= seq->last_line->address) {
    *filename_ptr = NULL;
    return false;
  }

  if (!build_line_info_table (table, seq)) {
    *filename_ptr = NULL;
    return false;
  }

  low = 0;
  high = seq->num_lines;
  while (low < high)
    {
      mid = (low + high) / 2;
      info = seq->line_info_lookup[mid];
      if (addr < info->address)
	high = mid;
      else if (mid + 1 < seq->num_lines && addr >= seq->line_info_lookup[mid + 1]->address)
	low = mid + 1;
      else
	break;
    }

  if (!info || low >= high || mid + 1 >= seq->num_lines) {
    *filename_ptr = NULL;
    return false;
  }

  if (addr >= info->address && 
      addr < seq->line_info_lookup[mid + 1]->address &&
      !info->end_sequence && 
      info != seq->last_line)
    {
      *filename_ptr = info->filename;
      *linenumber_ptr = info->line;
      if (discriminator_ptr)
	*discriminator_ptr = info->discriminator;
      return true;
    }

  *filename_ptr = NULL;
  return false;
}

/* Read in the .debug_ranges section for future reference.  */

static bool
read_debug_ranges (struct comp_unit * unit)
{
  if (unit == NULL || unit->stash == NULL || unit->file == NULL)
    return false;

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  if (file->syms == NULL)
    return false;

  return read_section (unit->abfd, &stash->debug_sections[debug_ranges],
		       file->syms, 0,
		       &file->dwarf_ranges_buffer, &file->dwarf_ranges_size);
}

/* Read in the .debug_rnglists section for future reference.  */

static bool read_debug_rnglists(struct comp_unit *unit)
{
    if (unit == NULL || unit->stash == NULL || unit->file == NULL) {
        return false;
    }

    struct dwarf2_debug *stash = unit->stash;
    struct dwarf2_debug_file *file = unit->file;

    if (unit->abfd == NULL || file->syms == NULL) {
        return false;
    }

    return read_section(unit->abfd, 
                       &stash->debug_sections[debug_rnglists],
                       file->syms, 
                       0,
                       &file->dwarf_rnglists_buffer, 
                       &file->dwarf_rnglists_size);
}

/* Function table functions.  */

static int
compare_lookup_funcinfos (const void * a, const void * b)
{
  const struct lookup_funcinfo * lookup1 = a;
  const struct lookup_funcinfo * lookup2 = b;

  if (lookup1->low_addr != lookup2->low_addr)
    return (lookup1->low_addr < lookup2->low_addr) ? -1 : 1;

  if (lookup1->high_addr != lookup2->high_addr)
    return (lookup1->high_addr < lookup2->high_addr) ? -1 : 1;

  if (lookup1->idx != lookup2->idx)
    return (lookup1->idx < lookup2->idx) ? -1 : 1;

  return 0;
}

static bool
build_lookup_funcinfo_table (struct comp_unit * unit)
{
  if (unit->lookup_funcinfo_table != NULL || unit->number_of_functions == 0)
    return true;

  struct lookup_funcinfo *lookup_funcinfo_table = 
    bfd_malloc (unit->number_of_functions * sizeof (struct lookup_funcinfo));
  if (lookup_funcinfo_table == NULL)
    return false;

  if (!populate_lookup_table(unit, lookup_funcinfo_table))
  {
    free(lookup_funcinfo_table);
    return false;
  }

  qsort (lookup_funcinfo_table,
         unit->number_of_functions,
         sizeof (struct lookup_funcinfo),
         compare_lookup_funcinfos);

  calculate_high_watermarks(lookup_funcinfo_table, unit->number_of_functions);

  unit->lookup_funcinfo_table = lookup_funcinfo_table;
  return true;
}

static bool
populate_lookup_table(struct comp_unit *unit, struct lookup_funcinfo *table)
{
  size_t func_index = unit->number_of_functions;
  struct funcinfo *each;

  for (each = unit->function_table; each != NULL; each = each->prev_func)
  {
    if (func_index == 0)
      return false;
    
    func_index--;
    initialize_lookup_entry(&table[func_index], each, func_index);
  }

  return func_index == 0;
}

static void
initialize_lookup_entry(struct lookup_funcinfo *entry, struct funcinfo *funcinfo, size_t idx)
{
  entry->funcinfo = funcinfo;
  entry->idx = idx;
  
  bfd_vma low_addr = funcinfo->arange.low;
  bfd_vma high_addr = funcinfo->arange.high;

  struct arange *range;
  for (range = funcinfo->arange.next; range != NULL; range = range->next)
  {
    if (range->low < low_addr)
      low_addr = range->low;
    if (range->high > high_addr)
      high_addr = range->high;
  }

  entry->low_addr = low_addr;
  entry->high_addr = high_addr;
}

static void
calculate_high_watermarks(struct lookup_funcinfo *table, unsigned int count)
{
  if (count == 0)
    return;

  bfd_vma high_addr = table[0].high_addr;
  
  for (unsigned int i = 1; i < count; i++)
  {
    if (table[i].high_addr > high_addr)
      high_addr = table[i].high_addr;
    else
      table[i].high_addr = high_addr;
  }
}

/* If ADDR is within UNIT's function tables, set FUNCTION_PTR, and return
   TRUE.  Note that we need to find the function that has the smallest range
   that contains ADDR, to handle inlined functions without depending upon
   them being ordered in TABLE by increasing range.  */

static bool
lookup_address_in_function_table (struct comp_unit *unit,
                                  bfd_vma addr,
                                  struct funcinfo **function_ptr)
{
  if (unit == NULL || function_ptr == NULL)
    return false;

  if (unit->number_of_functions == 0)
    return false;

  if (!build_lookup_funcinfo_table (unit))
    return false;

  if (unit->lookup_funcinfo_table[unit->number_of_functions - 1].high_addr < addr)
    return false;

  bfd_size_type first = find_first_matching_function(unit, addr);
  
  struct funcinfo *best_fit = find_best_fit_function(unit, addr, first);
  
  if (best_fit == NULL)
    return false;

  *function_ptr = best_fit;
  return true;
}

static bfd_size_type
find_first_matching_function(struct comp_unit *unit, bfd_vma addr)
{
  bfd_size_type low = 0;
  bfd_size_type high = unit->number_of_functions;
  bfd_size_type first = high;
  
  while (low < high)
    {
      bfd_size_type mid = low + (high - low) / 2;
      struct lookup_funcinfo *lookup_funcinfo = &unit->lookup_funcinfo_table[mid];
      
      if (addr < lookup_funcinfo->low_addr)
        high = mid;
      else if (addr >= lookup_funcinfo->high_addr)
        low = mid + 1;
      else
        {
          high = mid;
          first = mid;
        }
    }
  
  return first;
}

static struct funcinfo *
find_best_fit_function(struct comp_unit *unit, bfd_vma addr, bfd_size_type first)
{
  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;
  
  for (bfd_size_type i = first; i < unit->number_of_functions; i++)
    {
      if (addr < unit->lookup_funcinfo_table[i].low_addr)
        break;
        
      struct funcinfo *funcinfo = unit->lookup_funcinfo_table[i].funcinfo;
      
      if (funcinfo == NULL)
        continue;
        
      check_function_ranges(funcinfo, addr, &best_fit, &best_fit_len);
    }
  
  return best_fit;
}

static void
check_function_ranges(struct funcinfo *funcinfo, bfd_vma addr,
                      struct funcinfo **best_fit, bfd_vma *best_fit_len)
{
  for (struct arange *arange = &funcinfo->arange; arange != NULL; arange = arange->next)
    {
      if (addr < arange->low || addr >= arange->high)
        continue;
        
      bfd_vma range_len = arange->high - arange->low;
      
      if (is_better_fit(range_len, *best_fit_len, funcinfo, *best_fit))
        {
          *best_fit = funcinfo;
          *best_fit_len = range_len;
        }
    }
}

static bool
is_better_fit(bfd_vma range_len, bfd_vma best_fit_len,
              struct funcinfo *funcinfo, struct funcinfo *best_fit)
{
  if (range_len < best_fit_len)
    return true;
    
  if (range_len == best_fit_len && funcinfo > best_fit)
    return true;
    
  return false;
}

/* If SYM at ADDR is within function table of UNIT, set FILENAME_PTR
   and LINENUMBER_PTR, and return TRUE.  */

static bool
lookup_symbol_in_function_table (struct comp_unit *unit,
				 asymbol *sym,
				 bfd_vma addr,
				 const char **filename_ptr,
				 unsigned int *linenumber_ptr)
{
  if (unit == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

  const char *name = bfd_asymbol_name (sym);
  if (name == NULL)
    return false;

  struct funcinfo* best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  for (struct funcinfo* each = unit->function_table; each != NULL; each = each->prev_func)
    {
      if (each->file == NULL || each->name == NULL)
        continue;

      if (strstr (name, each->name) == NULL)
        continue;

      for (struct arange *arange = &each->arange; arange != NULL; arange = arange->next)
        {
          if (addr < arange->low || addr >= arange->high)
            continue;

          bfd_vma current_len = arange->high - arange->low;
          if (current_len < best_fit_len)
            {
              best_fit = each;
              best_fit_len = current_len;
            }
        }
    }

  if (best_fit != NULL)
    {
      *filename_ptr = best_fit->file;
      *linenumber_ptr = best_fit->line;
      return true;
    }

  return false;
}

/* Variable table functions.  */

/* If SYM is within variable table of UNIT, set FILENAME_PTR and
   LINENUMBER_PTR, and return TRUE.  */

static bool
lookup_symbol_in_variable_table(struct comp_unit *unit,
                                asymbol *sym,
                                bfd_vma addr,
                                const char **filename_ptr,
                                unsigned int *linenumber_ptr)
{
    if (unit == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL) {
        return false;
    }

    const char *name = bfd_asymbol_name(sym);
    if (name == NULL) {
        return false;
    }

    struct varinfo *each = unit->variable_table;
    while (each != NULL) {
        if (each->addr == addr &&
            !each->stack &&
            each->file != NULL &&
            each->name != NULL &&
            strstr(name, each->name) != NULL) {
            *filename_ptr = each->file;
            *linenumber_ptr = each->line;
            return true;
        }
        each = each->prev_var;
    }

    return false;
}

static struct comp_unit *stash_comp_unit (struct dwarf2_debug *,
					  struct dwarf2_debug_file *);
static bool comp_unit_maybe_decode_line_info (struct comp_unit *);

static bool
find_abstract_instance (struct comp_unit *unit,
			struct attribute *attr_ptr,
			unsigned int recur_count,
			const char **pname,
			bool *is_linkage,
			char **filename_ptr,
			int *linenumber_ptr)
{
  bfd *abfd = unit->abfd;
  bfd_byte *info_ptr = NULL;
  bfd_byte *info_ptr_end;
  unsigned int abbrev_number, i;
  struct abbrev_info *abbrev;
  uint64_t die_ref = attr_ptr->u.val;
  struct attribute attr;

  if (recur_count >= 100)
    {
      _bfd_error_handler
	(_("DWARF error: abstract instance recursion detected"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (attr_ptr->form == DW_FORM_ref_addr)
    {
      if (!handle_ref_addr_form(unit, die_ref, &info_ptr, &info_ptr_end))
        return false;
    }
  else if (attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      if (!handle_gnu_ref_alt_form(unit, die_ref, &info_ptr, &info_ptr_end))
        return false;
    }

  if (attr_ptr->form == DW_FORM_ref_addr || attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      if (!find_containing_unit(unit, attr_ptr->form, &info_ptr, &info_ptr_end, die_ref, &unit))
        return false;
    }
  else
    {
      if (!handle_relative_ref_form(unit, die_ref, &info_ptr, &info_ptr_end))
        return false;
    }

  abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
  if (abbrev_number)
    {
      abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
      if (!abbrev)
	{
	  _bfd_error_handler
	    (_("DWARF error: could not find abbrev number %u"), abbrev_number);
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
      
      if (!process_abbrev_attrs(abbrev, unit, &info_ptr, info_ptr_end, 
                                recur_count, pname, is_linkage, 
                                filename_ptr, linenumber_ptr))
        return false;
    }
  return true;
}

static bool
handle_ref_addr_form(struct comp_unit *unit, uint64_t die_ref, 
                     bfd_byte **info_ptr, bfd_byte **info_ptr_end)
{
  size_t total;
  
  *info_ptr = unit->file->dwarf_info_buffer;
  *info_ptr_end = *info_ptr + unit->file->dwarf_info_size;
  total = *info_ptr_end - *info_ptr;
  
  if (!die_ref)
    return true;
    
  if (die_ref >= total)
    {
      _bfd_error_handler
        (_("DWARF error: invalid abstract instance DIE ref"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  
  *info_ptr += die_ref;
  return true;
}

static bool
handle_gnu_ref_alt_form(struct comp_unit *unit, uint64_t die_ref,
                        bfd_byte **info_ptr, bfd_byte **info_ptr_end)
{
  bool first_time = unit->stash->alt.dwarf_info_buffer == NULL;
  
  *info_ptr = read_alt_indirect_ref (unit, die_ref);
  if (first_time)
    unit->stash->alt.info_ptr = unit->stash->alt.dwarf_info_buffer;
    
  if (*info_ptr == NULL)
    {
      _bfd_error_handler
        (_("DWARF error: unable to read alt ref %" PRIu64),
         (uint64_t) die_ref);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
    
  *info_ptr_end = (unit->stash->alt.dwarf_info_buffer
                  + unit->stash->alt.dwarf_info_size);
  if (unit->stash->alt.all_comp_units)
    unit = unit->stash->alt.all_comp_units;
    
  return true;
}

static bool
handle_relative_ref_form(struct comp_unit *unit, uint64_t die_ref,
                         bfd_byte **info_ptr, bfd_byte **info_ptr_end)
{
  size_t total;
  
  *info_ptr = unit->info_ptr_unit;
  *info_ptr_end = unit->end_ptr;
  total = *info_ptr_end - *info_ptr;
  
  if (!die_ref || die_ref >= total)
    {
      _bfd_error_handler
        (_("DWARF error: invalid abstract instance DIE ref"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
    
  *info_ptr += die_ref;
  return true;
}

static bool
find_containing_unit(struct comp_unit *unit, int form, bfd_byte **info_ptr,
                    bfd_byte **info_ptr_end, uint64_t die_ref, 
                    struct comp_unit **unit_out)
{
  if (*info_ptr >= unit->info_ptr_unit && *info_ptr < unit->end_ptr)
    {
      *info_ptr_end = unit->end_ptr;
      *unit_out = unit;
      return true;
    }
    
  struct comp_unit *u = NULL;
  struct addr_range range = { *info_ptr, *info_ptr };
  splay_tree_node v = splay_tree_lookup (unit->file->comp_unit_tree,
                                         (splay_tree_key)&range);
  if (v != NULL)
    u = (struct comp_unit *)v->value;
    
  if (u == NULL)
    {
      struct stash_file *file = (form == DW_FORM_ref_addr) 
                                ? &unit->stash->f 
                                : &unit->stash->alt;
      u = search_comp_units(unit->stash, file, *info_ptr);
    }
    
  if (u == NULL)
    {
      _bfd_error_handler
        (_("DWARF error: unable to locate abstract instance DIE ref %"
           PRIu64), (uint64_t) die_ref);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
    
  *unit_out = u;
  *info_ptr_end = u->end_ptr;
  return true;
}

static struct comp_unit *
search_comp_units(struct dwarf2_debug *stash, struct stash_file *file,
                 bfd_byte *target_ptr)
{
  struct comp_unit *u = NULL;
  
  while ((u = stash_comp_unit(stash, file)) != NULL)
    {
      if (target_ptr >= u->info_ptr_unit && target_ptr < u->end_ptr)
        return u;
    }
    
  return NULL;
}

static bool
process_abbrev_attrs(struct abbrev_info *abbrev, struct comp_unit *unit,
                    bfd_byte **info_ptr, bfd_byte *info_ptr_end,
                    unsigned int recur_count, const char **pname,
                    bool *is_linkage, char **filename_ptr, int *linenumber_ptr)
{
  struct attribute attr;
  unsigned int i;
  
  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      *info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit,
                                 *info_ptr, info_ptr_end);
      if (*info_ptr == NULL)
        break;
        
      if (!process_single_attr(&attr, unit, recur_count, pname,
                              is_linkage, filename_ptr, linenumber_ptr))
        return false;
    }
    
  return true;
}

static bool
process_single_attr(struct attribute *attr, struct comp_unit *unit,
                   unsigned int recur_count, const char **pname,
                   bool *is_linkage, char **filename_ptr, int *linenumber_ptr)
{
  switch (attr->name)
    {
    case DW_AT_name:
      if (*pname == NULL && is_str_form (attr))
        {
          *pname = attr->u.str;
          if (mangle_style (unit->lang) == 0)
            *is_linkage = true;
        }
      break;
      
    case DW_AT_specification:
      if (is_int_form (attr) &&
          !find_abstract_instance (unit, attr, recur_count + 1,
                                  pname, is_linkage,
                                  filename_ptr, linenumber_ptr))
        return false;
      break;
      
    case DW_AT_linkage_name:
    case DW_AT_MIPS_linkage_name:
      if (is_str_form (attr))
        {
          *pname = attr->u.str;
          *is_linkage = true;
        }
      break;
      
    case DW_AT_decl_file:
      if (!comp_unit_maybe_decode_line_info (unit))
        return false;
      if (is_int_form (attr))
        {
          free (*filename_ptr);
          *filename_ptr = concat_filename (unit->line_table, attr->u.val);
        }
      break;
      
    case DW_AT_decl_line:
      if (is_int_form (attr))
        *linenumber_ptr = attr->u.val;
      break;
      
    default:
      break;
    }
    
  return true;
}

static bool
read_ranges (struct comp_unit *unit, struct arange *arange,
	     struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *ranges_ptr;
  bfd_byte *ranges_end;
  bfd_vma base_address;
  bfd_vma low_pc;
  bfd_vma high_pc;
  size_t required_size;

  if (unit == NULL || unit->file == NULL)
    return false;

  base_address = unit->base_address;

  if (unit->file->dwarf_ranges_buffer == NULL)
    {
      if (!read_debug_ranges (unit))
	return false;
    }

  if (offset > unit->file->dwarf_ranges_size)
    return false;

  ranges_ptr = unit->file->dwarf_ranges_buffer + offset;
  ranges_end = unit->file->dwarf_ranges_buffer + unit->file->dwarf_ranges_size;

  while (ranges_ptr < ranges_end)
    {
      required_size = 2u * unit->addr_size;
      if (required_size > (size_t) (ranges_end - ranges_ptr))
	return false;

      low_pc = read_address (unit, &ranges_ptr, ranges_end);
      high_pc = read_address (unit, &ranges_ptr, ranges_end);

      if (low_pc == 0 && high_pc == 0)
	break;

      if (low_pc == (bfd_vma) -1 && high_pc != (bfd_vma) -1)
	{
	  base_address = high_pc;
	  continue;
	}

      if (!arange_add (unit, arange, trie_root,
		       base_address + low_pc, base_address + high_pc))
	return false;
    }

  return true;
}

static bool
read_rnglists (struct comp_unit *unit, struct arange *arange,
	       struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *rngs_ptr;
  bfd_byte *rngs_end;
  bfd_vma base_address = unit->base_address;
  bfd_vma low_pc;
  bfd_vma high_pc;
  bfd *abfd = unit->abfd;

  if (!unit->file->dwarf_rnglists_buffer)
    {
      if (!read_debug_rnglists (unit))
	return false;
    }

  if (offset > unit->file->dwarf_rnglists_size)
    return false;

  rngs_ptr = unit->file->dwarf_rnglists_buffer + offset;
  rngs_end = unit->file->dwarf_rnglists_buffer + unit->file->dwarf_rnglists_size;

  while (rngs_ptr < rngs_end)
    {
      enum dwarf_range_list_entry rlet;

      rlet = read_1_byte (abfd, &rngs_ptr, rngs_end);

      if (rlet == DW_RLE_end_of_list)
	return true;

      if (rlet == DW_RLE_base_address)
	{
	  if (unit->addr_size > (size_t) (rngs_end - rngs_ptr))
	    return false;
	  base_address = read_address (unit, &rngs_ptr, rngs_end);
	  continue;
	}

      if (!process_range_entry (unit, arange, trie_root, &rngs_ptr, rngs_end,
				 rlet, base_address))
	return false;
    }

  return false;
}

static bool
process_range_entry (struct comp_unit *unit, struct arange *arange,
		     struct trie_node **trie_root, bfd_byte **rngs_ptr,
		     bfd_byte *rngs_end, enum dwarf_range_list_entry rlet,
		     bfd_vma base_address)
{
  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bfd *abfd = unit->abfd;

  switch (rlet)
    {
    case DW_RLE_start_length:
      if (unit->addr_size > (size_t) (rngs_end - *rngs_ptr))
	return false;
      low_pc = read_address (unit, rngs_ptr, rngs_end);
      high_pc = low_pc + _bfd_safe_read_leb128 (abfd, rngs_ptr, false, rngs_end);
      break;

    case DW_RLE_offset_pair:
      low_pc = base_address + _bfd_safe_read_leb128 (abfd, rngs_ptr, false, rngs_end);
      high_pc = base_address + _bfd_safe_read_leb128 (abfd, rngs_ptr, false, rngs_end);
      break;

    case DW_RLE_start_end:
      if (2u * unit->addr_size > (size_t) (rngs_end - *rngs_ptr))
	return false;
      low_pc = read_address (unit, rngs_ptr, rngs_end);
      high_pc = read_address (unit, rngs_ptr, rngs_end);
      break;

    default:
      return false;
    }

  return arange_add (unit, arange, trie_root, low_pc, high_pc);
}

static bool
read_rangelist(struct comp_unit *unit, struct arange *arange,
               struct trie_node **trie_root, uint64_t offset)
{
    if (unit == NULL || arange == NULL || trie_root == NULL) {
        return false;
    }
    
    if (unit->version <= 4) {
        return read_ranges(unit, arange, trie_root, offset);
    }
    
    return read_rnglists(unit, arange, trie_root, offset);
}

static struct funcinfo *
lookup_func_by_offset (uint64_t offset, struct funcinfo * table)
{
  while (table != NULL)
    {
      if (table->unit_offset == offset)
        return table;
      table = table->prev_func;
    }
  return NULL;
}

static struct varinfo *
lookup_var_by_offset (uint64_t offset, struct varinfo * table)
{
  for (struct varinfo *current = table; current != NULL; current = current->prev_var)
    {
      if (current->unit_offset == offset)
        return current;
    }

  return NULL;
}


/* DWARF2 Compilation unit functions.  */

static struct funcinfo *
reverse_funcinfo_list (struct funcinfo *head)
{
  struct funcinfo *rhead = NULL;
  struct funcinfo *temp = NULL;

  while (head != NULL)
    {
      temp = head->prev_func;
      head->prev_func = rhead;
      rhead = head;
      head = temp;
    }
  return rhead;
}

static struct varinfo *reverse_varinfo_list(struct varinfo *head)
{
    struct varinfo *reversed = NULL;
    struct varinfo *current = head;
    
    while (current != NULL)
    {
        struct varinfo *next = current->prev_var;
        current->prev_var = reversed;
        reversed = current;
        current = next;
    }
    
    return reversed;
}

/* Scan over each die in a comp. unit looking for functions to add
   to the function table and variables to the variable table.  */

static bool
scan_unit_for_symbols (struct comp_unit *unit)
{
  bfd *abfd = unit->abfd;
  bfd_byte *info_ptr = unit->first_child_die_ptr;
  bfd_byte *info_ptr_end = unit->end_ptr;
  int nesting_level = 0;
  struct nest_funcinfo
  {
    struct funcinfo *func;
  } *nested_funcs;
  int nested_funcs_size;
  struct funcinfo *last_func;
  struct varinfo *last_var;
  bool result = false;
  
  nested_funcs_size = 32;
  nested_funcs = (struct nest_funcinfo *)
    bfd_malloc (nested_funcs_size * sizeof (*nested_funcs));
  if (nested_funcs == NULL)
    return false;
  nested_funcs[nesting_level].func = 0;

  if (!scan_dies_first_pass(unit, &info_ptr, info_ptr_end, &nesting_level, 
                            &nested_funcs, &nested_funcs_size))
    goto cleanup;

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  info_ptr = unit->first_child_die_ptr;
  nesting_level = 0;
  last_func = NULL;
  last_var = NULL;

  if (!scan_dies_second_pass(unit, &info_ptr, info_ptr_end, &nesting_level,
                             &last_func, &last_var))
    goto cleanup;

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);
  result = true;

cleanup:
  free (nested_funcs);
  return result;
}

static bool
scan_dies_first_pass(struct comp_unit *unit, bfd_byte **info_ptr_p,
                     bfd_byte *info_ptr_end, int *nesting_level_p,
                     struct nest_funcinfo **nested_funcs_p, int *nested_funcs_size_p)
{
  bfd *abfd = unit->abfd;
  
  while (*nesting_level_p >= 0)
    {
      unsigned int abbrev_number;
      struct abbrev_info *abbrev;
      uint64_t current_offset;

      if (*info_ptr_p >= info_ptr_end)
        return false;

      current_offset = *info_ptr_p - unit->info_ptr_unit;
      abbrev_number = _bfd_safe_read_leb128 (abfd, info_ptr_p,
                                             false, info_ptr_end);
      if (abbrev_number == 0)
        {
          (*nesting_level_p)--;
          continue;
        }

      abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
      if (!validate_abbrev(abbrev, abbrev_number))
        return false;

      if (!process_die_first_pass(unit, abbrev, current_offset, 
                                  *nesting_level_p, *nested_funcs_p))
        return false;

      if (!skip_die_attributes(unit, abbrev, info_ptr_p, info_ptr_end))
        return false;

      if (abbrev->has_children)
        {
          (*nesting_level_p)++;
          if (!expand_nested_funcs_if_needed(nesting_level_p, nested_funcs_p, 
                                             nested_funcs_size_p))
            return false;
        }
    }
  return true;
}

static bool
scan_dies_second_pass(struct comp_unit *unit, bfd_byte **info_ptr_p,
                      bfd_byte *info_ptr_end, int *nesting_level_p,
                      struct funcinfo **last_func_p, struct varinfo **last_var_p)
{
  bfd *abfd = unit->abfd;
  
  while (*nesting_level_p >= 0)
    {
      unsigned int abbrev_number;
      struct abbrev_info *abbrev;
      uint64_t current_offset;
      struct funcinfo *func = NULL;
      struct varinfo *var = NULL;
      bfd_vma low_pc = 0;
      bfd_vma high_pc = 0;
      bool high_pc_relative = false;

      if (*info_ptr_p >= info_ptr_end)
        return false;

      current_offset = *info_ptr_p - unit->info_ptr_unit;
      abbrev_number = _bfd_safe_read_leb128 (abfd, info_ptr_p,
                                             false, info_ptr_end);
      if (!abbrev_number)
        {
          (*nesting_level_p)--;
          continue;
        }

      abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
      if (abbrev == NULL)
        return false;

      if (!find_die_info(abbrev, current_offset, unit, last_func_p, 
                        last_var_p, &func, &var))
        return false;

      if (!process_die_attributes(unit, abbrev, info_ptr_p, info_ptr_end,
                                  func, var, &low_pc, &high_pc, &high_pc_relative))
        return false;

      if (abbrev->has_children)
        (*nesting_level_p)++;

      if (high_pc_relative)
        high_pc += low_pc;

      if (func && high_pc != 0)
        {
          if (!arange_add (unit, &func->arange, &unit->file->trie_root,
                          low_pc, high_pc))
            return false;
        }
    }
  return true;
}

static bool
validate_abbrev(struct abbrev_info *abbrev, unsigned int abbrev_number)
{
  if (!abbrev)
    {
      static unsigned int previous_failed_abbrev = -1U;
      if (abbrev_number != previous_failed_abbrev)
        {
          _bfd_error_handler
            (_("DWARF error: could not find abbrev number %u"),
             abbrev_number);
          previous_failed_abbrev = abbrev_number;
        }
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
process_die_first_pass(struct comp_unit *unit, struct abbrev_info *abbrev,
                       uint64_t current_offset, int nesting_level,
                       struct nest_funcinfo *nested_funcs)
{
  if (abbrev->tag == DW_TAG_subprogram
      || abbrev->tag == DW_TAG_entry_point
      || abbrev->tag == DW_TAG_inlined_subroutine)
    {
      struct funcinfo *func = (struct funcinfo *) bfd_zalloc (unit->abfd, 
                                                              sizeof (struct funcinfo));
      if (func == NULL)
        return false;
      func->tag = abbrev->tag;
      func->prev_func = unit->function_table;
      func->unit_offset = current_offset;
      unit->function_table = func;
      unit->number_of_functions++;

      if (func->tag == DW_TAG_inlined_subroutine)
        {
          for (int i = nesting_level; i-- != 0; )
            if (nested_funcs[i].func)
              {
                func->caller_func = nested_funcs[i].func;
                break;
              }
        }
      nested_funcs[nesting_level].func = func;
    }
  else
    {
      if (abbrev->tag == DW_TAG_variable || abbrev->tag == DW_TAG_member)
        {
          struct varinfo *var = (struct varinfo *) bfd_zalloc (unit->abfd, 
                                                               sizeof (struct varinfo));
          if (var == NULL)
            return false;
          var->tag = abbrev->tag;
          var->stack = true;
          var->prev_var = unit->variable_table;
          unit->variable_table = var;
          var->unit_offset = current_offset;
        }
      nested_funcs[nesting_level].func = 0;
    }
  return true;
}

static bool
skip_die_attributes(struct comp_unit *unit, struct abbrev_info *abbrev,
                   bfd_byte **info_ptr_p, bfd_byte *info_ptr_end)
{
  for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      *info_ptr_p = read_attribute (&attr, &abbrev->attrs[i],
                                   unit, *info_ptr_p, info_ptr_end);
      if (*info_ptr_p == NULL)
        return false;
    }
  return true;
}

static bool
expand_nested_funcs_if_needed(int *nesting_level_p,
                              struct nest_funcinfo **nested_funcs_p,
                              int *nested_funcs_size_p)
{
  if (*nesting_level_p >= *nested_funcs_size_p)
    {
      *nested_funcs_size_p *= 2;
      struct nest_funcinfo *tmp = (struct nest_funcinfo *)
        bfd_realloc (*nested_funcs_p,
                    *nested_funcs_size_p * sizeof (**nested_funcs_p));
      if (tmp == NULL)
        return false;
      *nested_funcs_p = tmp;
    }
  (*nested_funcs_p)[*nesting_level_p].func = 0;
  return true;
}

static bool
find_die_info(struct abbrev_info *abbrev, uint64_t current_offset,
             struct comp_unit *unit, struct funcinfo **last_func_p,
             struct varinfo **last_var_p, struct funcinfo **func_p,
             struct varinfo **var_p)
{
  if (abbrev->tag == DW_TAG_subprogram
      || abbrev->tag == DW_TAG_entry_point
      || abbrev->tag == DW_TAG_inlined_subroutine)
    {
      if (*last_func_p
          && (*last_func_p)->prev_func
          && (*last_func_p)->prev_func->unit_offset == current_offset)
        *func_p = (*last_func_p)->prev_func;
      else
        *func_p = lookup_func_by_offset (current_offset, unit->function_table);

      if (*func_p == NULL)
        return false;

      *last_func_p = *func_p;
    }
  else if (abbrev->tag == DW_TAG_variable || abbrev->tag == DW_TAG_member)
    {
      if (*last_var_p
          && (*last_var_p)->prev_var
          && (*last_var_p)->prev_var->unit_offset == current_offset)
        *var_p = (*last_var_p)->prev_var;
      else
        *var_p = lookup_var_by_offset (current_offset, unit->variable_table);

      if (*var_p == NULL)
        return false;

      *last_var_p = *var_p;
    }
  return true;
}

static bool
process_die_attributes(struct comp_unit *unit, struct abbrev_info *abbrev,
                       bfd_byte **info_ptr_p, bfd_byte *info_ptr_end,
                       struct funcinfo *func, struct varinfo *var,
                       bfd_vma *low_pc_p, bfd_vma *high_pc_p,
                       bool *high_pc_relative_p)
{
  for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      *info_ptr_p = read_attribute (&attr, &abbrev->attrs[i],
                                   unit, *info_ptr_p, info_ptr_end);
      if (*info_ptr_p == NULL)
        return false;

      if (func)
        {
          if (!process_func_attribute(unit, func, &attr, low_pc_p, 
                                      high_pc_p, high_pc_relative_p))
            return false;
        }
      else if (var)
        {
          process_var_attribute(unit, var, &attr);
        }
    }
  return true;
}

static bool
process_func_attribute(struct comp_unit *unit, struct funcinfo *func,
                       struct attribute *attr, bfd_vma *low_pc_p,
                       bfd_vma *high_pc_p, bool *high_pc_relative_p)
{
  switch (attr->name)
    {
    case DW_AT_call_file:
      if (is_int_form (attr))
        {
          free (func->caller_file);
          func->caller_file = concat_filename (unit->line_table, attr->u.val);
        }
      break;

    case DW_AT_call_line:
      if (is_int_form (attr))
        func->caller_line = attr->u.val;
      break;

    case DW_AT_abstract_origin:
    case DW_AT_specification:
      if (is_int_form (attr)
          && !find_abstract_instance (unit, attr, 0,
                                      &func->name,
                                      &func->is_linkage,
                                      &func->file,
                                      &func->line))
        return false;
      break;

    case DW_AT_name:
      if (func->name == NULL && is_str_form (attr))
        {
          func->name = attr->u.str;
          if (mangle_style (unit->lang) == 0)
            func->is_linkage = true;
        }
      break;

    case DW_AT_linkage_name:
    case DW_AT_MIPS_linkage_name:
      if (is_str_form (attr))
        {
          func->name = attr->u.str;
          func->is_linkage = true;
        }
      break;

    case DW_AT_low_pc:
      if (is_int_form (attr))
        *low_pc_p = attr->u.val;
      break;

    case DW_AT_high_pc:
      if (is_int_form (attr))
        {
          *high_pc_p = attr->u.val;
          *high_pc_relative_p = attr->form != DW_FORM_addr;
        }
      break;

    case DW_AT_ranges:
      if (is_int_form (attr)
          && !read_rangelist (unit, &func->arange,
                             &unit->file->trie_root, attr->u.val))
        return false;
      break;

    case DW_AT_decl_file:
      if (is_int_form (attr))
        {
          free (func->file);
          func->file = concat_filename (unit->line_table, attr->u.val);
        }
      break;

    case DW_AT_decl_line:
      if (is_int_form (attr))
        func->line = attr->u.val;
      break;

    default:
      break;
    }
  return true;
}

static void
process_var_attribute(struct comp_unit *unit, struct varinfo *var,
                     struct attribute *attr)
{
  switch (attr->name)
    {
    case DW_AT_specification:
      if (is_int_form (attr) && attr->u.val)
        {
          bool is_linkage;
          if (!find_abstract_instance (unit, attr, 0,
                                       &var->name,
                                       &is_linkage,
                                       &var->file,
                                       &var->line))
            {
              _bfd_error_handler (_("DWARF error: could not find "
                                   "variable specification "
                                   "at offset 0x%lx"),
                                 (unsigned long) attr->u.val);
            }
        }
      break;

    case DW_AT_name:
      if (is_str_form (attr))
        var->name = attr->u.str;
      break;

    case DW_AT_decl_file:
      if (is_int_form (attr))
        {
          free (var->file);
          var->file = concat_filename (unit->line_table, attr->u.val);
        }
      break;

    case DW_AT_decl_line:
      if (is_int_form (attr))
        var->line = attr->u.val;
      break;

    case DW_AT_external:
      if (is_int_form (attr) && attr->u.val != 0)
        var->stack = false;
      break;

    case DW_AT_location:
      process_var_location(unit, var, attr);
      break;

    default:
      break;
    }
}

static void
process_var_location(struct comp_unit *unit, struct varinfo *var,
                    struct attribute *attr)
{
  switch (attr->form)
    {
    case DW_FORM_block:
    case DW_FORM_block1:
    case DW_FORM_block2:
    case DW_FORM_block4:
    case DW_FORM_exprloc:
      if (attr->u.blk->data != NULL
          && *attr->u.blk->data == DW_OP_addr)
        {
          var->stack = false;
          if (attr->u.blk->size == unit->addr_size + 1U)
            var->addr = bfd_get (unit->addr_size * 8,
                                unit->abfd,
                                attr->u.blk->data + 1);
        }
      break;

    default:
      break;
    }
}

/* Read the attributes of the form strx and addrx.  */

static void
reread_attribute (struct comp_unit *unit,
		  struct attribute *attr,
		  bfd_vma *low_pc,
		  bfd_vma *high_pc,
		  bool *high_pc_relative,
		  bool compunit)
{
  if (unit == NULL || attr == NULL || low_pc == NULL || 
      high_pc == NULL || high_pc_relative == NULL)
    return;

  if (is_strx_form (attr->form))
    attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
  if (is_addrx_form (attr->form))
    attr->u.val = read_indexed_address (attr->u.val, unit);

  switch (attr->name)
    {
    case DW_AT_stmt_list:
      unit->stmtlist = 1;
      unit->line_offset = attr->u.val;
      break;

    case DW_AT_name:
      if (is_str_form (attr))
	unit->name = attr->u.str;
      break;

    case DW_AT_low_pc:
      *low_pc = attr->u.val;
      if (compunit)
	unit->base_address = *low_pc;
      break;

    case DW_AT_high_pc:
      *high_pc = attr->u.val;
      *high_pc_relative = attr->form != DW_FORM_addr;
      break;

    case DW_AT_ranges:
      read_rangelist (unit, &unit->arange,
		      &unit->file->trie_root, attr->u.val);
      break;

    case DW_AT_comp_dir:
      if (!is_str_form (attr))
	{
	  _bfd_error_handler
	    (_("DWARF error: DW_AT_comp_dir attribute encountered "
	       "with a non-string form"));
	  unit->comp_dir = NULL;
	}
      else
	{
	  char *comp_dir = attr->u.str;
	  if (comp_dir != NULL)
	    {
	      char *cp = strchr (comp_dir, ':');
	      if (cp != NULL && cp != comp_dir && cp > comp_dir && 
		  cp[-1] == '.' && cp[1] == '/')
		comp_dir = cp + 1;
	    }
	  unit->comp_dir = comp_dir;
	}
      break;

    case DW_AT_language:
      unit->lang = attr->u.val;
      break;

    default:
      break;
    }
}

/* Parse a DWARF2 compilation unit starting at INFO_PTR.  UNIT_LENGTH
   includes the compilation unit header that proceeds the DIE's, but
   does not include the length field that precedes each compilation
   unit header.  END_PTR points one past the end of this comp unit.
   OFFSET_SIZE is the size of DWARF2 offsets (either 4 or 8 bytes).

   This routine does not read the whole compilation unit; only enough
   to get to the line number information for the compilation unit.  */

static struct comp_unit *
parse_comp_unit (struct dwarf2_debug *stash,
		 struct dwarf2_debug_file *file,
		 bfd_byte *info_ptr,
		 bfd_vma unit_length,
		 bfd_byte *info_ptr_unit,
		 unsigned int offset_size)
{
  struct comp_unit* unit;
  unsigned int version;
  uint64_t abbrev_offset = 0;
  unsigned int addr_size = 0;
  struct abbrev_info** abbrevs;
  unsigned int abbrev_number, i;
  struct abbrev_info *abbrev;
  struct attribute attr;
  bfd_byte *end_ptr = info_ptr + unit_length;
  size_t amt;
  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bfd *abfd = file->bfd_ptr;
  bool high_pc_relative = false;
  enum dwarf_unit_type unit_type;
  struct attribute *str_addrp = NULL;
  size_t str_count = 0;
  size_t str_alloc = 0;
  bool compunit_flag = false;

  version = read_2_bytes (abfd, &info_ptr, end_ptr);
  if (version < 2 || version > 5)
    {
      if (version)
	{
	  _bfd_error_handler
	    (_("DWARF error: found dwarf version '%u', this reader"
	       " only handles version 2, 3, 4 and 5 information"), version);
	  bfd_set_error (bfd_error_bad_value);
	}
      return NULL;
    }

  if (version < 5)
    unit_type = DW_UT_compile;
  else
    {
      unit_type = read_1_byte (abfd, &info_ptr, end_ptr);
      addr_size = read_1_byte (abfd, &info_ptr, end_ptr);
    }

  BFD_ASSERT (offset_size == 4 || offset_size == 8);
  if (offset_size == 4)
    abbrev_offset = read_4_bytes (abfd, &info_ptr, end_ptr);
  else
    abbrev_offset = read_8_bytes (abfd, &info_ptr, end_ptr);

  if (version < 5)
    addr_size = read_1_byte (abfd, &info_ptr, end_ptr);

  switch (unit_type)
    {
    case DW_UT_type:
      info_ptr += 8;
      info_ptr += offset_size;
      break;

    case DW_UT_skeleton:
      info_ptr += 8;
      break;

    default:
      break;
    }

  if (addr_size > sizeof (bfd_vma))
    {
      _bfd_error_handler
	(_("DWARF error: found address size '%u', this reader"
	   " can not handle sizes greater than '%u'"),
	 addr_size,
	 (unsigned int) sizeof (bfd_vma));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  if (addr_size != 2 && addr_size != 4 && addr_size != 8)
    {
      _bfd_error_handler
	("DWARF error: found address size '%u', this reader"
	 " can only handle address sizes '2', '4' and '8'", addr_size);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  abbrevs = read_abbrevs (abfd, abbrev_offset, stash, file);
  if (!abbrevs)
    return NULL;

  abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr,
					 false, end_ptr);
  if (!abbrev_number)
    return NULL;

  abbrev = lookup_abbrev (abbrev_number, abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"),
			  abbrev_number);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  amt = sizeof (struct comp_unit);
  unit = (struct comp_unit *) bfd_zalloc (abfd, amt);
  if (unit == NULL)
    return NULL;
  unit->abfd = abfd;
  unit->version = version;
  unit->addr_size = addr_size;
  unit->offset_size = offset_size;
  unit->abbrevs = abbrevs;
  unit->end_ptr = end_ptr;
  unit->stash = stash;
  unit->file = file;
  unit->info_ptr_unit = info_ptr_unit;

  if (abbrev->tag == DW_TAG_compile_unit)
    compunit_flag = true;

  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit, info_ptr, end_ptr);
      if (info_ptr == NULL)
	goto err_exit;

      if ((unit->dwarf_str_offset == 0 && is_strx_form (attr.form))
	  || (unit->dwarf_addr_offset == 0 && is_addrx_form (attr.form)))
	{
	  if (str_count >= str_alloc)
	    {
	      str_alloc = 2 * str_alloc + 200;
	      struct attribute *new_str_addrp = bfd_realloc (str_addrp,
				       str_alloc * sizeof (*str_addrp));
	      if (new_str_addrp == NULL)
		goto err_exit;
	      str_addrp = new_str_addrp;
	    }
	  str_addrp[str_count] = attr;
	  str_count++;
	  continue;
	}

      switch (attr.name)
	{
	case DW_AT_stmt_list:
	  if (is_int_form (&attr))
	    {
	      unit->stmtlist = 1;
	      unit->line_offset = attr.u.val;
	    }
	  break;

	case DW_AT_name:
	  if (is_str_form (&attr))
	    unit->name = attr.u.str;
	  break;

	case DW_AT_low_pc:
	  if (is_int_form (&attr))
	    {
	      low_pc = attr.u.val;
	      if (compunit_flag)
		unit->base_address = low_pc;
	    }
	  break;

	case DW_AT_high_pc:
	  if (is_int_form (&attr))
	    {
	      high_pc = attr.u.val;
	      high_pc_relative = attr.form != DW_FORM_addr;
	    }
	  break;

	case DW_AT_ranges:
	  if (is_int_form (&attr)
	      && !read_rangelist (unit, &unit->arange,
				  &unit->file->trie_root, attr.u.val))
	    goto err_exit;
	  break;

	case DW_AT_comp_dir:
	  {
	    char *comp_dir = attr.u.str;

	    if (!is_str_form (&attr))
	      {
		_bfd_error_handler
		  (_("DWARF error: DW_AT_comp_dir attribute encountered with a non-string form"));
		comp_dir = NULL;
	      }

	    if (comp_dir)
	      {
		char *cp = strchr (comp_dir, ':');

		if (cp && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
		  comp_dir = cp + 1;
	      }
	    unit->comp_dir = comp_dir;
	    break;
	  }

	case DW_AT_language:
	  if (is_int_form (&attr))
	    unit->lang = attr.u.val;
	  break;

	case DW_AT_addr_base:
	  unit->dwarf_addr_offset = attr.u.val;
	  break;

	case DW_AT_str_offsets_base:
	  unit->dwarf_str_offset = attr.u.val;
	  break;

	default:
	  break;
	}
    }

  for (i = 0; i < str_count; ++i)
    reread_attribute (unit, &str_addrp[i], &low_pc, &high_pc,
		      &high_pc_relative, compunit_flag);

  if (high_pc_relative)
    high_pc += low_pc;
  if (high_pc != 0)
    {
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
		       low_pc, high_pc))
	goto err_exit;
    }

  unit->first_child_die_ptr = info_ptr;

  free (str_addrp);
  return unit;

 err_exit:
  unit->error = 1;
  free (str_addrp);
  return NULL;
}

/* Return TRUE if UNIT may contain the address given by ADDR.  When
   there are functions written entirely with inline asm statements, the
   range info in the compilation unit header may not be correct.  We
   need to consult the line info table to see if a compilation unit
   really contains the given address.  */

static bool
comp_unit_may_contain_address (struct comp_unit *unit, bfd_vma addr)
{
  struct arange *arange;

  if (unit == NULL || unit->error)
    return false;

  if (unit->arange.high == 0 || unit->line_table == NULL)
    return true;

  arange = &unit->arange;
  while (arange != NULL)
  {
    if (addr >= arange->low && addr < arange->high)
      return true;
    arange = arange->next;
  }

  return false;
}

/* If UNIT contains ADDR, set the output parameters to the values for
   the line containing ADDR and return TRUE.  Otherwise return FALSE.
   The output parameters, FILENAME_PTR, FUNCTION_PTR, and
   LINENUMBER_PTR, are pointers to the objects to be filled in.  */

static bool
comp_unit_find_nearest_line (struct comp_unit *unit,
                             bfd_vma addr,
                             const char **filename_ptr,
                             struct funcinfo **function_ptr,
                             unsigned int *linenumber_ptr,
                             unsigned int *discriminator_ptr)
{
  if (unit == NULL || function_ptr == NULL)
    return false;

  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  *function_ptr = NULL;
  bool func_p = lookup_address_in_function_table (unit, addr, function_ptr);

  if (func_p && *function_ptr != NULL && (*function_ptr)->tag == DW_TAG_inlined_subroutine)
  {
    if (unit->stash != NULL)
      unit->stash->inliner_chain = *function_ptr;
  }

  bool line_p = false;
  if (unit->line_table != NULL)
  {
    line_p = lookup_address_in_line_info_table (unit->line_table, addr,
                                                filename_ptr,
                                                linenumber_ptr,
                                                discriminator_ptr);
  }

  return line_p || func_p;
}

/* Check to see if line info is already decoded in a comp_unit.
   If not, decode it.  Returns TRUE if no errors were encountered;
   FALSE otherwise.  */

static bool
comp_unit_maybe_decode_line_info (struct comp_unit *unit)
{
  if (unit->error)
    return false;

  if (unit->line_table)
    return true;

  if (!unit->stmtlist)
    {
      unit->error = 1;
      return false;
    }

  unit->line_table = decode_line_info (unit);
  if (!unit->line_table)
    {
      unit->error = 1;
      return false;
    }

  if (unit->first_child_die_ptr < unit->end_ptr && !scan_unit_for_symbols (unit))
    {
      unit->error = 1;
      return false;
    }

  return true;
}

/* If UNIT contains SYM at ADDR, set the output parameters to the
   values for the line containing SYM.  The output parameters,
   FILENAME_PTR, and LINENUMBER_PTR, are pointers to the objects to be
   filled in.

   Return TRUE if UNIT contains SYM, and no errors were encountered;
   FALSE otherwise.  */

static bool
comp_unit_find_line (struct comp_unit *unit,
		     asymbol *sym,
		     bfd_vma addr,
		     const char **filename_ptr,
		     unsigned int *linenumber_ptr)
{
  if (unit == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  bool is_function = (sym->flags & BSF_FUNCTION) != 0;
  
  if (is_function)
    return lookup_symbol_in_function_table (unit, sym, addr,
					    filename_ptr,
					    linenumber_ptr);

  return lookup_symbol_in_variable_table (unit, sym, addr,
					  filename_ptr,
					  linenumber_ptr);
}

/* Extract all interesting funcinfos and varinfos of a compilation
   unit into hash tables for faster lookup.  Returns TRUE if no
   errors were enountered; FALSE otherwise.  */

static bool
comp_unit_hash_info (struct dwarf2_debug *stash,
		     struct comp_unit *unit,
		     struct info_hash_table *funcinfo_hash_table,
		     struct info_hash_table *varinfo_hash_table)
{
  BFD_ASSERT (stash->info_hash_status != STASH_INFO_HASH_DISABLED);

  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  BFD_ASSERT (!unit->cached);

  if (!hash_function_table(unit, funcinfo_hash_table))
    return false;

  if (!hash_variable_table(unit, varinfo_hash_table))
    return false;

  unit->cached = true;
  return true;
}

static bool
hash_function_table(struct comp_unit *unit,
                   struct info_hash_table *funcinfo_hash_table)
{
  struct funcinfo* each_func;
  bool result = true;

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  
  for (each_func = unit->function_table;
       each_func != NULL && result;
       each_func = each_func->prev_func)
    {
      if (each_func->name != NULL)
        {
          result = insert_info_hash_table (funcinfo_hash_table, 
                                          each_func->name,
                                          (void*) each_func, 
                                          false);
        }
    }
  
  unit->function_table = reverse_funcinfo_list (unit->function_table);
  return result;
}

static bool
hash_variable_table(struct comp_unit *unit,
                   struct info_hash_table *varinfo_hash_table)
{
  struct varinfo* each_var;
  bool result = true;

  unit->variable_table = reverse_varinfo_list (unit->variable_table);
  
  for (each_var = unit->variable_table;
       each_var != NULL && result;
       each_var = each_var->prev_var)
    {
      if (!each_var->stack && 
          each_var->file != NULL && 
          each_var->name != NULL)
        {
          result = insert_info_hash_table (varinfo_hash_table, 
                                          each_var->name,
                                          (void*) each_var, 
                                          false);
        }
    }
  
  unit->variable_table = reverse_varinfo_list (unit->variable_table);
  return result;
}

/* Locate a section in a BFD containing debugging info.  The search starts
   from the section after AFTER_SEC, or from the first section in the BFD if
   AFTER_SEC is NULL.  The search works by examining the names of the
   sections.  There are three permissiable names.  The first two are given
   by DEBUG_SECTIONS[debug_info] (whose standard DWARF2 names are .debug_info
   and .zdebug_info).  The third is a prefix .gnu.linkonce.wi.
   This is a variation on the .debug_info section which has a checksum
   describing the contents appended onto the name.  This allows the linker to
   identify and discard duplicate debugging sections for different
   compilation units.  */
#define GNU_LINKONCE_INFO ".gnu.linkonce.wi."

static asection *
find_debug_info (bfd *abfd, const struct dwarf_debug_section *debug_sections,
		 asection *after_sec)
{
  asection *msec;
  const char *uncompressed_name;
  const char *compressed_name;

  if (abfd == NULL || debug_sections == NULL)
    return NULL;

  uncompressed_name = debug_sections[debug_info].uncompressed_name;
  compressed_name = debug_sections[debug_info].compressed_name;

  if (after_sec == NULL)
    {
      msec = bfd_get_section_by_name (abfd, uncompressed_name);
      if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
	return msec;

      if (compressed_name != NULL)
	{
	  msec = bfd_get_section_by_name (abfd, compressed_name);
	  if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
	    return msec;
	}

      for (msec = abfd->sections; msec != NULL; msec = msec->next)
	{
	  if ((msec->flags & SEC_HAS_CONTENTS) != 0
	      && startswith (msec->name, GNU_LINKONCE_INFO))
	    return msec;
	}

      return NULL;
    }

  for (msec = after_sec->next; msec != NULL; msec = msec->next)
    {
      if ((msec->flags & SEC_HAS_CONTENTS) == 0)
	continue;

      if (strcmp (msec->name, uncompressed_name) == 0)
	return msec;

      if (compressed_name != NULL && strcmp (msec->name, compressed_name) == 0)
	return msec;

      if (startswith (msec->name, GNU_LINKONCE_INFO))
	return msec;
    }

  return NULL;
}

/* Transfer VMAs from object file to separate debug file.  */

static void
set_debug_vma (bfd *orig_bfd, bfd *debug_bfd)
{
  asection *s;
  asection *d;

  if (orig_bfd == NULL || debug_bfd == NULL)
    return;

  s = orig_bfd->sections;
  d = debug_bfd->sections;

  while (s != NULL && d != NULL)
    {
      if ((d->flags & SEC_DEBUGGING) != 0)
        return;

      if (s->name != NULL && d->name != NULL && strcmp (s->name, d->name) == 0)
        {
          d->output_section = s->output_section;
          d->output_offset = s->output_offset;
          d->vma = s->vma;
        }

      s = s->next;
      d = d->next;
    }
}

/* If the dwarf2 info was found in a separate debug file, return the
   debug file section corresponding to the section in the original file
   and the debug file symbols.  */

static void
_bfd_dwarf2_stash_syms (struct dwarf2_debug *stash, bfd *abfd,
			asection **sec, asymbol ***syms)
{
  if (stash == NULL || sec == NULL || syms == NULL || stash->f.bfd_ptr == abfd)
    return;

  if (*sec == NULL)
    {
      *syms = stash->f.syms;
      return;
    }

  asection *s = abfd->sections;
  asection *d = stash->f.bfd_ptr->sections;

  while (s != NULL && d != NULL)
    {
      if ((d->flags & SEC_DEBUGGING) != 0)
        return;

      if (s == *sec && strcmp(s->name, d->name) == 0)
        {
          *sec = d;
          *syms = stash->f.syms;
          return;
        }

      s = s->next;
      d = d->next;
    }
}

/* Unset vmas for adjusted sections in STASH.  */

static void unset_sections(struct dwarf2_debug *stash)
{
    if (!stash || !stash->adjusted_sections) {
        return;
    }
    
    for (int i = 0; i < stash->adjusted_section_count; i++) {
        struct adjusted_section *p = &stash->adjusted_sections[i];
        if (p && p->section) {
            p->section->vma = p->orig_vma;
        }
    }
}

/* Set VMAs for allocated and .debug_info sections in ORIG_BFD, a
   relocatable object file.  VMAs are normally all zero in relocatable
   object files, so if we want to distinguish locations in sections by
   address we need to set VMAs so the sections do not overlap.  We
   also set VMA on .debug_info so that when we have multiple
   .debug_info sections (or the linkonce variant) they also do not
   overlap.  The multiple .debug_info sections make up a single
   logical section.  ??? We should probably do the same for other
   debug sections.  */

static bool
place_sections (bfd *orig_bfd, struct dwarf2_debug *stash)
{
  if (stash->adjusted_section_count != 0)
    {
      struct adjusted_section *p = stash->adjusted_sections;
      for (int i = stash->adjusted_section_count; i > 0; i--, p++)
        p->section->vma = p->adj_vma;
      return true;
    }

  const char *debug_info_name = stash->debug_sections[debug_info].uncompressed_name;
  int section_count = 0;
  
  for (bfd *abfd = orig_bfd; ; abfd = stash->f.bfd_ptr)
    {
      for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
        {
          if (sect->output_section != NULL && 
              sect->output_section != sect && 
              (sect->flags & SEC_DEBUGGING) == 0)
            continue;

          bool is_debug_info = (strcmp (sect->name, debug_info_name) == 0 ||
                                startswith (sect->name, GNU_LINKONCE_INFO));
          bool is_alloc_in_orig = (sect->flags & SEC_ALLOC) != 0 && abfd == orig_bfd;

          if (is_debug_info || is_alloc_in_orig)
            section_count++;
        }
      
      if (abfd == stash->f.bfd_ptr)
        break;
    }

  if (section_count <= 1)
    {
      stash->adjusted_section_count = -1;
      return true;
    }

  size_t amt = section_count * sizeof (struct adjusted_section);
  struct adjusted_section *sections = (struct adjusted_section *) bfd_malloc (amt);
  if (sections == NULL)
    return false;

  stash->adjusted_sections = sections;
  stash->adjusted_section_count = section_count;

  bfd_vma last_vma = 0;
  bfd_vma last_dwarf = 0;
  struct adjusted_section *current = sections;

  for (bfd *abfd = orig_bfd; ; abfd = stash->f.bfd_ptr)
    {
      for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
        {
          if (sect->output_section != NULL && 
              sect->output_section != sect && 
              (sect->flags & SEC_DEBUGGING) == 0)
            continue;

          bool is_debug_info = (strcmp (sect->name, debug_info_name) == 0 ||
                                startswith (sect->name, GNU_LINKONCE_INFO));
          bool is_alloc_in_orig = (sect->flags & SEC_ALLOC) != 0 && abfd == orig_bfd;

          if (!is_debug_info && !is_alloc_in_orig)
            continue;

          bfd_size_type sz = sect->rawsize ? sect->rawsize : sect->size;
          current->section = sect;
          current->orig_vma = sect->vma;

          bfd_vma *target_vma = is_debug_info ? &last_dwarf : &last_vma;
          bfd_vma mask = ((bfd_vma) 1 << sect->alignment_power) - 1;
          *target_vma = (*target_vma + mask) & ~mask;
          
          sect->vma = *target_vma;
          *target_vma += sz;
          current->adj_vma = sect->vma;
          current++;
        }
      
      if (abfd == stash->f.bfd_ptr)
        break;
    }

  if (orig_bfd != stash->f.bfd_ptr)
    set_debug_vma (orig_bfd, stash->f.bfd_ptr);

  return true;
}

/* Look up a funcinfo by name using the given info hash table.  If found,
   also update the locations pointed to by filename_ptr and linenumber_ptr.

   This function returns TRUE if a funcinfo that matches the given symbol
   and address is found with any error; otherwise it returns FALSE.  */

static bool
info_hash_lookup_funcinfo (struct info_hash_table *hash_table,
			   asymbol *sym,
			   bfd_vma addr,
			   const char **filename_ptr,
			   unsigned int *linenumber_ptr)
{
  if (!hash_table || !sym || !filename_ptr || !linenumber_ptr)
    return false;

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    return false;

  struct funcinfo* best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  struct info_list_node *node = lookup_info_hash_table (hash_table, name);
  while (node)
    {
      struct funcinfo* each_func = (struct funcinfo *) node->info;
      if (each_func)
        {
          struct arange *arange = &each_func->arange;
          while (arange)
            {
              if (addr >= arange->low && addr < arange->high)
                {
                  bfd_vma range_len = arange->high - arange->low;
                  if (range_len < best_fit_len)
                    {
                      best_fit = each_func;
                      best_fit_len = range_len;
                    }
                }
              arange = arange->next;
            }
        }
      node = node->next;
    }

  if (!best_fit)
    return false;

  *filename_ptr = best_fit->file;
  *linenumber_ptr = best_fit->line;
  return true;
}

/* Look up a varinfo by name using the given info hash table.  If found,
   also update the locations pointed to by filename_ptr and linenumber_ptr.

   This function returns TRUE if a varinfo that matches the given symbol
   and address is found with any error; otherwise it returns FALSE.  */

static bool
info_hash_lookup_varinfo (struct info_hash_table *hash_table,
			  asymbol *sym,
			  bfd_vma addr,
			  const char **filename_ptr,
			  unsigned int *linenumber_ptr)
{
  if (!hash_table || !sym || !filename_ptr || !linenumber_ptr)
    return false;

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    return false;

  struct info_list_node *node = lookup_info_hash_table (hash_table, name);
  
  while (node)
    {
      struct varinfo *each = (struct varinfo *) node->info;
      if (each && each->addr == addr)
	{
	  *filename_ptr = each->file;
	  *linenumber_ptr = each->line;
	  return true;
	}
      node = node->next;
    }

  return false;
}

/* Update the funcinfo and varinfo info hash tables if they are
   not up to date.  Returns TRUE if there is no error; otherwise
   returns FALSE and disable the info hash tables.  */

static bool
stash_maybe_update_info_hash_tables (struct dwarf2_debug *stash)
{
  struct comp_unit *each;

  if (stash == NULL)
    return false;

  if (stash->f.all_comp_units == stash->hash_units_head)
    return true;

  each = (stash->hash_units_head != NULL) 
         ? stash->hash_units_head->prev_unit 
         : stash->f.last_comp_unit;

  while (each != NULL)
    {
      if (!comp_unit_hash_info (stash, each, stash->funcinfo_hash_table,
				stash->varinfo_hash_table))
	{
	  stash->info_hash_status = STASH_INFO_HASH_DISABLED;
	  return false;
	}
      each = each->prev_unit;
    }

  stash->hash_units_head = stash->f.all_comp_units;
  return true;
}

/* Check consistency of info hash tables.  This is for debugging only.  */

static void ATTRIBUTE_UNUSED
stash_verify_info_hash_table (struct dwarf2_debug *stash)
{
  struct comp_unit *each_unit;
  struct funcinfo *each_func;
  struct varinfo *each_var;
  struct info_list_node *node;
  bool found;

  for (each_unit = stash->f.all_comp_units;
       each_unit;
       each_unit = each_unit->next_unit)
    {
      for (each_func = each_unit->function_table;
	   each_func;
	   each_func = each_func->prev_func)
	{
	  if (!each_func->name)
	    continue;
	  node = lookup_info_hash_table (stash->funcinfo_hash_table,
					 each_func->name);
	  BFD_ASSERT (node);
	  found = false;
	  while (node && !found)
	    {
	      found = node->info == each_func;
	      node = node->next;
	    }
	  BFD_ASSERT (found);
	}

      for (each_var = each_unit->variable_table;
	   each_var;
	   each_var = each_var->prev_var)
	{
	  if (!each_var->name || !each_var->file || each_var->stack)
	    continue;
	  node = lookup_info_hash_table (stash->varinfo_hash_table,
					 each_var->name);
	  BFD_ASSERT (node);
	  found = false;
	  while (node && !found)
	    {
	      found = node->info == each_var;
	      node = node->next;
	    }
	  BFD_ASSERT (found);
	}
    }
}

/* Check to see if we want to enable the info hash tables, which consume
   quite a bit of memory.  Currently we only check the number times
   bfd_dwarf2_find_line is called.  In the future, we may also want to
   take the number of symbols into account.  */

static void
stash_maybe_enable_info_hash_tables (bfd *abfd, struct dwarf2_debug *stash)
{
  BFD_ASSERT (stash->info_hash_status == STASH_INFO_HASH_OFF);

  if (stash->info_hash_count++ < STASH_INFO_HASH_TRIGGER)
    return;

  stash->funcinfo_hash_table = create_info_hash_table (abfd);
  if (!stash->funcinfo_hash_table)
    {
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
      return;
    }

  stash->varinfo_hash_table = create_info_hash_table (abfd);
  if (!stash->varinfo_hash_table)
    {
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
      return;
    }

  if (stash_maybe_update_info_hash_tables (stash))
    stash->info_hash_status = STASH_INFO_HASH_ON;
}

/* Find the file and line associated with a symbol and address using the
   info hash tables of a stash. If there is a match, the function returns
   TRUE and update the locations pointed to by filename_ptr and linenumber_ptr;
   otherwise it returns FALSE.  */

static bool
stash_find_line_fast (struct dwarf2_debug *stash,
		      asymbol *sym,
		      bfd_vma addr,
		      const char **filename_ptr,
		      unsigned int *linenumber_ptr)
{
  if (stash == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

  if (stash->info_hash_status != STASH_INFO_HASH_ON)
    return false;

  if ((sym->flags & BSF_FUNCTION) != 0)
    return info_hash_lookup_funcinfo (stash->funcinfo_hash_table, sym, addr,
				      filename_ptr, linenumber_ptr);
  
  return info_hash_lookup_varinfo (stash->varinfo_hash_table, sym, addr,
				   filename_ptr, linenumber_ptr);
}

/* Save current section VMAs.  */

static bool
save_section_vma (const bfd *abfd, struct dwarf2_debug *stash)
{
  asection *s;
  unsigned int i;

  if (abfd == NULL || stash == NULL)
    return false;

  if (abfd->section_count == 0)
    return true;

  stash->sec_vma = bfd_malloc (sizeof (*stash->sec_vma) * abfd->section_count);
  if (stash->sec_vma == NULL)
    return false;

  stash->sec_vma_count = abfd->section_count;
  
  for (i = 0, s = abfd->sections; s != NULL && i < abfd->section_count; i++, s = s->next)
    {
      stash->sec_vma[i] = (s->output_section != NULL) 
                          ? (s->output_section->vma + s->output_offset)
                          : s->vma;
    }
    
  return true;
}

/* Compare current section VMAs against those at the time the stash
   was created.  If find_nearest_line is used in linker warnings or
   errors early in the link process, the debug info stash will be
   invalid for later calls.  This is because we relocate debug info
   sections, so the stashed section contents depend on symbol values,
   which in turn depend on section VMAs.  */

static bool
section_vma_same (const bfd *abfd, const struct dwarf2_debug *stash)
{
  asection *s;
  unsigned int i;

  if (abfd == NULL || stash == NULL)
    return false;

  if (abfd->section_count != stash->sec_vma_count)
    return false;

  if (stash->sec_vma == NULL)
    return false;

  s = abfd->sections;
  for (i = 0; i < abfd->section_count && s != NULL; i++)
    {
      bfd_vma vma;

      if (s->output_section != NULL)
        vma = s->output_section->vma + s->output_offset;
      else
        vma = s->vma;
      
      if (vma != stash->sec_vma[i])
        return false;
      
      s = s->next;
    }
  
  if (i != abfd->section_count || s != NULL)
    return false;
  
  return true;
}

/* Read debug information from DEBUG_BFD when DEBUG_BFD is specified.
   If DEBUG_BFD is not specified, we read debug information from ABFD
   or its gnu_debuglink. The results will be stored in PINFO.
   The function returns TRUE iff debug information is ready.  */

bool
_bfd_dwarf2_slurp_debug_info (bfd *abfd, bfd *debug_bfd,
			      const struct dwarf_debug_section *debug_sections,
			      asymbol **symbols,
			      void **pinfo,
			      bool do_place)
{
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;

  if (stash != NULL)
    {
      if (stash->orig_bfd_id == abfd->id && section_vma_same (abfd, stash))
	{
	  if (stash->f.dwarf_info_size == 0)
	    return false;
	  if (do_place && !place_sections (abfd, stash))
	    return false;
	  return true;
	}
      _bfd_dwarf2_cleanup_debug_info (abfd, pinfo);
      memset (stash, 0, sizeof (*stash));
    }
  else
    {
      stash = (struct dwarf2_debug *) bfd_zalloc (abfd, sizeof (*stash));
      if (stash == NULL)
	return false;
      *pinfo = stash;
    }

  stash->orig_bfd_id = abfd->id;
  stash->debug_sections = debug_sections;
  stash->f.syms = symbols;
  
  if (!save_section_vma (abfd, stash))
    return false;

  stash->f.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev,
					       del_abbrev, calloc, free);
  if (stash->f.abbrev_offsets == NULL)
    return false;

  stash->alt.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev,
						 del_abbrev, calloc, free);
  if (stash->alt.abbrev_offsets == NULL)
    return false;

  stash->f.trie_root = alloc_trie_leaf (abfd);
  if (stash->f.trie_root == NULL)
    return false;

  stash->alt.trie_root = alloc_trie_leaf (abfd);
  if (stash->alt.trie_root == NULL)
    return false;

  if (debug_bfd == NULL)
    debug_bfd = abfd;

  asection *msec = find_debug_info (debug_bfd, debug_sections, NULL);
  
  if (msec == NULL && abfd == debug_bfd)
    {
      char *debug_filename = bfd_follow_build_id_debuglink (abfd, DEBUGDIR);
      if (debug_filename == NULL)
	debug_filename = bfd_follow_gnu_debuglink (abfd, DEBUGDIR);

      if (debug_filename == NULL)
	return false;

      debug_bfd = bfd_openr (debug_filename, NULL);
      free (debug_filename);
      
      if (debug_bfd == NULL)
	return false;

      debug_bfd->flags |= BFD_DECOMPRESS;
      
      if (!bfd_check_format (debug_bfd, bfd_object))
	{
	  bfd_close (debug_bfd);
	  return false;
	}
      
      msec = find_debug_info (debug_bfd, debug_sections, NULL);
      if (msec == NULL || !bfd_generic_link_read_symbols (debug_bfd))
	{
	  bfd_close (debug_bfd);
	  return false;
	}

      symbols = bfd_get_outsymbols (debug_bfd);
      stash->f.syms = symbols;
      stash->close_on_cleanup = true;
    }
  
  stash->f.bfd_ptr = debug_bfd;

  if (do_place && !place_sections (abfd, stash))
    return false;

  bfd_size_type total_size = 0;
  
  if (!find_debug_info (debug_bfd, debug_sections, msec))
    {
      total_size = bfd_get_section_limit_octets (debug_bfd, msec);
      if (!read_section (debug_bfd, &stash->debug_sections[debug_info],
			  symbols, 0,
			  &stash->f.dwarf_info_buffer, &total_size))
	{
	  unset_sections (stash);
	  return false;
	}
    }
  else
    {
      for (asection *current = msec; current != NULL; 
           current = find_debug_info (debug_bfd, debug_sections, current))
	{
	  if (bfd_section_size_insane (debug_bfd, current))
	    {
	      unset_sections (stash);
	      return false;
	    }
	  
	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, current);
	  
	  if (total_size > SIZE_MAX - readsz)
	    {
	      bfd_set_error (bfd_error_no_memory);
	      unset_sections (stash);
	      return false;
	    }
	  total_size += readsz;
	}

      stash->f.dwarf_info_buffer = (bfd_byte *) bfd_malloc (total_size);
      if (stash->f.dwarf_info_buffer == NULL)
	{
	  unset_sections (stash);
	  return false;
	}

      total_size = 0;
      for (asection *current = find_debug_info (debug_bfd, debug_sections, NULL);
	   current != NULL;
	   current = find_debug_info (debug_bfd, debug_sections, current))
	{
	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, current);
	  if (readsz == 0)
	    continue;

	  if (!bfd_simple_get_relocated_section_contents
		(debug_bfd, current, stash->f.dwarf_info_buffer + total_size,
		 symbols))
	    {
	      unset_sections (stash);
	      return false;
	    }

	  total_size += readsz;
	}
    }

  stash->f.info_ptr = stash->f.dwarf_info_buffer;
  stash->f.dwarf_info_size = total_size;
  return true;
}

/* Parse the next DWARF2 compilation unit at FILE->INFO_PTR.  */

static struct comp_unit *
stash_comp_unit (struct dwarf2_debug *stash, struct dwarf2_debug_file *file)
{
  bfd_size_type length;
  unsigned int offset_size;
  bfd_byte *info_ptr_unit = file->info_ptr;
  bfd_byte *info_ptr_end = file->dwarf_info_buffer + file->dwarf_info_size;

  if (file->info_ptr >= info_ptr_end)
    return NULL;

  length = read_4_bytes (file->bfd_ptr, &file->info_ptr, info_ptr_end);
  
  if (length == 0xffffffff)
    {
      offset_size = 8;
      length = read_8_bytes (file->bfd_ptr, &file->info_ptr, info_ptr_end);
    }
  else if (length == 0)
    {
      offset_size = 8;
      length = read_4_bytes (file->bfd_ptr, &file->info_ptr, info_ptr_end);
    }
  else
    {
      offset_size = 4;
    }

  if (length == 0 || length > (size_t) (info_ptr_end - file->info_ptr))
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  struct comp_unit *each = parse_comp_unit (stash, file,
                                            file->info_ptr, length,
                                            info_ptr_unit, offset_size);
  if (each == NULL)
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  if (file->comp_unit_tree == NULL)
    {
      file->comp_unit_tree = splay_tree_new (splay_tree_compare_addr_range,
                                             splay_tree_free_addr_range, NULL);
      if (file->comp_unit_tree == NULL)
        {
          file->info_ptr = info_ptr_end;
          return NULL;
        }
    }

  struct addr_range *r = (struct addr_range *)bfd_malloc (sizeof (struct addr_range));
  if (r == NULL)
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  r->start = each->info_ptr_unit;
  r->end = each->end_ptr;
  
  if (r->end <= r->start)
    {
      free (r);
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  splay_tree_node v = splay_tree_lookup (file->comp_unit_tree, (splay_tree_key)r);
  if (v != NULL)
    {
      free (r);
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  splay_tree_insert (file->comp_unit_tree, (splay_tree_key)r, (splay_tree_value)each);

  if (file->all_comp_units)
    file->all_comp_units->prev_unit = each;
  else
    file->last_comp_unit = each;

  each->next_unit = file->all_comp_units;
  file->all_comp_units = each;

  if (each->arange.high == 0)
    {
      each->next_unit_without_ranges = file->all_comp_units_without_ranges;
      file->all_comp_units_without_ranges = each->next_unit_without_ranges;
    }

  file->info_ptr += length;
  return each;
}

/* Hash function for an asymbol.  */

static hashval_t
hash_asymbol (const void *sym)
{
  if (sym == NULL)
    return 0;
  
  const asymbol *asym = sym;
  
  if (asym->name == NULL)
    return 0;
  
  return htab_hash_string (asym->name);
}

/* Equality function for asymbols.  */

static int
eq_asymbol (const void *a, const void *b)
{
  if (a == NULL || b == NULL) {
    return 0;
  }
  
  const asymbol *sa = a;
  const asymbol *sb = b;
  
  if (sa->name == NULL || sb->name == NULL) {
    return (sa->name == sb->name) ? 1 : 0;
  }
  
  return strcmp (sa->name, sb->name) == 0;
}

/* Scan the debug information in PINFO looking for a DW_TAG_subprogram
   abbrev with a DW_AT_low_pc attached to it.  Then lookup that same
   symbol in SYMBOLS and return the difference between the low_pc and
   the symbol's address.  Returns 0 if no suitable symbol could be found.  */

bfd_signed_vma
_bfd_dwarf2_find_symbol_bias (asymbol ** symbols, void ** pinfo)
{
  struct dwarf2_debug *stash;
  struct comp_unit * unit;
  htab_t sym_hash;
  bfd_signed_vma result = 0;
  asymbol ** psym;

  if (pinfo == NULL)
    return 0;
    
  stash = (struct dwarf2_debug *) *pinfo;
  
  if (stash == NULL || symbols == NULL)
    return 0;

  sym_hash = htab_create_alloc (10, hash_asymbol, eq_asymbol,
				NULL, xcalloc, free);
  if (sym_hash == NULL)
    return 0;
    
  for (psym = symbols; * psym != NULL; psym++)
    {
      asymbol * sym = * psym;

      if ((sym->flags & BSF_FUNCTION) && sym->section != NULL)
	{
	  void **slot = htab_find_slot (sym_hash, sym, INSERT);
	  if (slot != NULL)
	    *slot = sym;
	}
    }

  for (unit = stash->f.all_comp_units; unit != NULL; unit = unit->next_unit)
    {
      struct funcinfo * func;

      comp_unit_maybe_decode_line_info (unit);

      for (func = unit->function_table; func != NULL; func = func->prev_func)
	{
	  if (func->name != NULL && func->arange.low != 0)
	    {
	      asymbol search;
	      asymbol *sym;

	      search.name = func->name;
	      sym = htab_find (sym_hash, &search);
	      if (sym != NULL)
		{
		  result = func->arange.low - (sym->value + sym->section->vma);
		  htab_delete (sym_hash);
		  return result;
		}
	    }
	}
    }

  htab_delete (sym_hash);
  return result;
}

/* See _bfd_dwarf2_find_nearest_line_with_alt.  */

int
_bfd_dwarf2_find_nearest_line (bfd *abfd,
                               asymbol **symbols,
                               asymbol *symbol,
                               asection *section,
                               bfd_vma offset,
                               const char **filename_ptr,
                               const char **functionname_ptr,
                               unsigned int *linenumber_ptr,
                               unsigned int *discriminator_ptr,
                               const struct dwarf_debug_section *debug_sections,
                               void **pinfo)
{
  if (abfd == NULL || section == NULL || filename_ptr == NULL ||
      functionname_ptr == NULL || linenumber_ptr == NULL ||
      discriminator_ptr == NULL || pinfo == NULL)
    {
      return 0;
    }

  return _bfd_dwarf2_find_nearest_line_with_alt
    (abfd, NULL, symbols, symbol, section, offset, filename_ptr,
     functionname_ptr, linenumber_ptr, discriminator_ptr, debug_sections,
     pinfo);
}

/* Find the source code location of SYMBOL.  If SYMBOL is NULL
   then find the nearest source code location corresponding to
   the address SECTION + OFFSET.
   Returns 1 if the line is found without error and fills in
   FILENAME_PTR and LINENUMBER_PTR.  In the case where SYMBOL was
   NULL the FUNCTIONNAME_PTR is also filled in.
   Returns 2 if partial information from _bfd_elf_find_function is
   returned (function and maybe file) by looking at symbols.  DWARF2
   info is present but not regarding the requested code location.
   Returns 0 otherwise.
   SYMBOLS contains the symbol table for ABFD.
   DEBUG_SECTIONS contains the name of the dwarf debug sections.
   If ALT_FILENAME is given, attempt to open the file and use it
   as the .gnu_debugaltlink file. Otherwise this file will be
   searched for when needed.  */

int
_bfd_dwarf2_find_nearest_line_with_alt
  (bfd *abfd,
   const char *alt_filename,
   asymbol **symbols,
   asymbol *symbol,
   asection *section,
   bfd_vma offset,
   const char **filename_ptr,
   const char **functionname_ptr,
   unsigned int *linenumber_ptr,
   unsigned int *discriminator_ptr,
   const struct dwarf_debug_section *debug_sections,
   void **pinfo)
{
  struct dwarf2_debug *stash;
  bfd_vma addr;
  struct comp_unit* each;
  struct funcinfo *function = NULL;
  int found = false;
  bool do_line;

  *filename_ptr = NULL;
  if (functionname_ptr != NULL)
    *functionname_ptr = NULL;
  *linenumber_ptr = 0;
  if (discriminator_ptr)
    *discriminator_ptr = 0;

  if (! _bfd_dwarf2_slurp_debug_info (abfd, NULL, debug_sections,
				      symbols, pinfo,
				      (abfd->flags & (EXEC_P | DYNAMIC)) == 0))
    return false;

  stash = (struct dwarf2_debug *) *pinfo;

  if (stash->alt.bfd_ptr == NULL && alt_filename != NULL)
    {
      if (!open_alt_bfd(stash, alt_filename))
        return false;
    }

  do_line = symbol != NULL;
  if (do_line)
    {
      BFD_ASSERT (section == NULL && offset == 0 && functionname_ptr == NULL);
      section = bfd_asymbol_section (symbol);
      addr = symbol->value;
    }
  else
    {
      BFD_ASSERT (section != NULL && functionname_ptr != NULL);
      addr = offset;
      check_data_symbol(abfd, section, offset, symbols, &symbol, &do_line);
    }

  addr = calculate_address(section, addr);

  if (! stash->f.info_ptr)
    return false;

  stash->inliner_chain = NULL;

  if (do_line)
    {
      found = search_line_info(stash, symbol, addr, filename_ptr, linenumber_ptr);
      if (found)
        goto done;
    }
  else
    {
      found = search_nearest_line(stash, addr, filename_ptr, &function, 
                                  linenumber_ptr, discriminator_ptr);
      if (found)
        goto done;
    }

  found = search_remaining_units(stash, do_line, symbol, addr, filename_ptr,
                                 &function, linenumber_ptr, discriminator_ptr);

 done:
  update_function_name(functionname_ptr, function, &found, symbols, 
                      abfd, section, offset, filename_ptr, stash);

  unset_sections (stash);

  return found;
}

static bool open_alt_bfd(struct dwarf2_debug *stash, const char *alt_filename)
{
  bfd *alt_bfd = bfd_openr (alt_filename, NULL);

  if (alt_bfd == NULL)
    return false;
    
  if (!bfd_check_format (alt_bfd, bfd_object))
    {
      bfd_set_error (bfd_error_wrong_format);
      bfd_close (alt_bfd);
      return false;
    }

  stash->alt.bfd_ptr = alt_bfd;
  return true;
}

static void check_data_symbol(bfd *abfd, asection *section, bfd_vma offset,
                              asymbol **symbols, asymbol **symbol, bool *do_line)
{
  if (symbols == NULL || (section->flags & SEC_CODE) != 0)
    return;

  for (asymbol **tmp = symbols; *tmp != NULL; ++tmp)
    {
      if ((*tmp)->the_bfd != abfd || (*tmp)->section != section ||
          (*tmp)->value != offset || ((*tmp)->flags & BSF_SECTION_SYM) != 0)
        continue;
        
      *symbol = *tmp;
      *do_line = true;
      
      if (((*symbol)->flags & BSF_GLOBAL) != 0)
        break;
    }
}

static bfd_vma calculate_address(asection *section, bfd_vma addr)
{
  if (section->output_section)
    return addr + section->output_section->vma + section->output_offset;
  return addr + section->vma;
}

static int search_line_info(struct dwarf2_debug *stash, asymbol *symbol, 
                            bfd_vma addr, const char **filename_ptr,
                            unsigned int *linenumber_ptr)
{
  int found = false;
  
  if (stash->info_hash_status == STASH_INFO_HASH_OFF)
    stash_maybe_enable_info_hash_tables (NULL, stash);

  if (stash->info_hash_status == STASH_INFO_HASH_ON)
    stash_maybe_update_info_hash_tables (stash);

  if (stash->info_hash_status == STASH_INFO_HASH_ON)
    {
      found = stash_find_line_fast (stash, symbol, addr,
                                   filename_ptr, linenumber_ptr);
      if (found)
        return found;
    }

  for (struct comp_unit *each = stash->f.all_comp_units; each; each = each->next_unit)
    {
      if ((symbol->flags & BSF_FUNCTION) == 0 ||
          comp_unit_may_contain_address (each, addr))
        {
          found = comp_unit_find_line (each, symbol, addr, filename_ptr,
                                      linenumber_ptr);
          if (found)
            return found;
        }
    }
  
  return false;
}

static int search_nearest_line(struct dwarf2_debug *stash, bfd_vma addr,
                               const char **filename_ptr, struct funcinfo **function,
                               unsigned int *linenumber_ptr, 
                               unsigned int *discriminator_ptr)
{
  int found = false;
  
  found = search_trie_ranges(stash, addr, filename_ptr, function,
                             linenumber_ptr, discriminator_ptr);
  if (found)
    return found;

  return search_units_without_ranges(stash, addr, filename_ptr, function,
                                     linenumber_ptr, discriminator_ptr);
}

static int search_trie_ranges(struct dwarf2_debug *stash, bfd_vma addr,
                              const char **filename_ptr, struct funcinfo **function,
                              unsigned int *linenumber_ptr,
                              unsigned int *discriminator_ptr)
{
  struct trie_node *trie = stash->f.trie_root;
  unsigned int bits = VMA_BITS - 8;

  while (trie && trie->num_room_in_leaf == 0)
    {
      int ch = (addr >> bits) & 0xff;
      trie = ((struct trie_interior *) trie)->children[ch];
      bits -= 8;
    }

  if (!trie)
    return false;

  const struct trie_leaf *leaf = (struct trie_leaf *) trie;
  
  for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
    leaf->ranges[i].unit->mark = false;

  for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
    {
      struct comp_unit *unit = leaf->ranges[i].unit;
      if (unit->mark || addr < leaf->ranges[i].low_pc ||
          addr >= leaf->ranges[i].high_pc)
        continue;
        
      unit->mark = true;
      
      if (comp_unit_find_nearest_line (unit, addr, filename_ptr, function,
                                       linenumber_ptr, discriminator_ptr))
        return true;
    }
    
  return false;
}

static int search_units_without_ranges(struct dwarf2_debug *stash, bfd_vma addr,
                                       const char **filename_ptr, 
                                       struct funcinfo **function,
                                       unsigned int *linenumber_ptr,
                                       unsigned int *discriminator_ptr)
{
  struct comp_unit **prev_each = &stash->f.all_comp_units_without_ranges;
  
  for (struct comp_unit *each = *prev_each; each; each = each->next_unit_without_ranges)
    {
      if (each->arange.high != 0)
        {
          *prev_each = each->next_unit_without_ranges;
          continue;
        }

      if (comp_unit_find_nearest_line (each, addr, filename_ptr, function,
                                       linenumber_ptr, discriminator_ptr))
        return true;
        
      prev_each = &each->next_unit_without_ranges;
    }
    
  return false;
}

static int search_remaining_units(struct dwarf2_debug *stash, bool do_line,
                                  asymbol *symbol, bfd_vma addr,
                                  const char **filename_ptr,
                                  struct funcinfo **function,
                                  unsigned int *linenumber_ptr,
                                  unsigned int *discriminator_ptr)
{
  struct comp_unit *each;
  
  while ((each = stash_comp_unit (stash, &stash->f)) != NULL)
    {
      int found = false;
      
      if (do_line)
        {
          if ((symbol->flags & BSF_FUNCTION) == 0 ||
              comp_unit_may_contain_address (each, addr))
            {
              found = comp_unit_find_line (each, symbol, addr,
                                          filename_ptr, linenumber_ptr);
            }
        }
      else
        {
          if (comp_unit_may_contain_address (each, addr))
            {
              found = comp_unit_find_nearest_line (each, addr, filename_ptr,
                                                  function, linenumber_ptr,
                                                  discriminator_ptr);
            }
        }

      if (found)
        return found;
    }
    
  return false;
}

static void update_function_name(const char **functionname_ptr,
                                 struct funcinfo *function, int *found,
                                 asymbol **symbols, bfd *abfd,
                                 asection *section, bfd_vma offset,
                                 const char **filename_ptr,
                                 struct dwarf2_debug *stash)
{
  if (!functionname_ptr)
    return;
    
  if (function && function->is_linkage)
    {
      *functionname_ptr = function->name;
      if (!*found)
        *found = 2;
      return;
    }
    
  if (!*functionname_ptr || (function && !function->is_linkage))
    {
      handle_elf_function(abfd, symbols, section, offset, filename_ptr,
                         functionname_ptr, stash, found, function);
    }
}

static void handle_elf_function(bfd *abfd, asymbol **symbols, asection *section,
                                bfd_vma offset, const char **filename_ptr,
                                const char **functionname_ptr,
                                struct dwarf2_debug *stash, int *found,
                                struct funcinfo *function)
{
  asymbol *fun;
  asymbol **syms = symbols;
  asection *sec = section;

  _bfd_dwarf2_stash_syms (stash, abfd, &sec, &syms);
  fun = _bfd_elf_find_function (abfd, syms, sec, offset,
                                *filename_ptr ? NULL : filename_ptr,
                                functionname_ptr);

  if (!*found && fun != NULL)
    *found = 2;

  if (function && !function->is_linkage)
    {
      bfd_vma sec_vma = section->vma;
      if (section->output_section != NULL)
        sec_vma = section->output_section->vma + section->output_offset;
        
      if (fun == NULL)
        *functionname_ptr = function->name;
      else if (fun->value + sec_vma == function->arange.low)
        function->name = *functionname_ptr;
        
      function->is_linkage = true;
    }
}

bool
_bfd_dwarf2_find_inliner_info (bfd *abfd ATTRIBUTE_UNUSED,
			       const char **filename_ptr,
			       const char **functionname_ptr,
			       unsigned int *linenumber_ptr,
			       void **pinfo)
{
  if (pinfo == NULL || filename_ptr == NULL || 
      functionname_ptr == NULL || linenumber_ptr == NULL)
    {
      return false;
    }

  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;
  if (stash == NULL)
    {
      return false;
    }

  struct funcinfo *func = stash->inliner_chain;
  if (func == NULL || func->caller_func == NULL)
    {
      return false;
    }

  *filename_ptr = func->caller_file;
  *functionname_ptr = func->caller_func->name;
  *linenumber_ptr = func->caller_line;
  stash->inliner_chain = func->caller_func;
  
  return true;
}

void
_bfd_dwarf2_cleanup_debug_info (bfd *abfd, void **pinfo)
{
  struct dwarf2_debug *stash;
  
  if (abfd == NULL || pinfo == NULL || *pinfo == NULL)
    return;
    
  stash = (struct dwarf2_debug *) *pinfo;

  if (stash->varinfo_hash_table)
    bfd_hash_table_free (&stash->varinfo_hash_table->base);
  if (stash->funcinfo_hash_table)
    bfd_hash_table_free (&stash->funcinfo_hash_table->base);

  cleanup_debug_file(&stash->f);
  cleanup_debug_file(&stash->alt);

  free (stash->sec_vma);
  free (stash->adjusted_sections);
  if (stash->close_on_cleanup)
    bfd_close (stash->f.bfd_ptr);
  if (stash->alt.bfd_ptr)
    bfd_close (stash->alt.bfd_ptr);
}

static void
cleanup_debug_file(struct dwarf2_debug_file *file)
{
  struct comp_unit *each;
  
  if (file == NULL)
    return;

  for (each = file->all_comp_units; each; each = each->next_unit)
    {
      cleanup_comp_unit_tables(each, file);
      cleanup_function_table(each->function_table);
      cleanup_variable_table(each->variable_table);
    }

  if (file->line_table)
    {
      free (file->line_table->files);
      free (file->line_table->dirs);
    }
    
  if (file->abbrev_offsets)
    htab_delete (file->abbrev_offsets);
  if (file->comp_unit_tree != NULL)
    splay_tree_delete (file->comp_unit_tree);

  free (file->dwarf_line_str_buffer);
  free (file->dwarf_str_buffer);
  free (file->dwarf_ranges_buffer);
  free (file->dwarf_rnglists_buffer);
  free (file->dwarf_line_buffer);
  free (file->dwarf_abbrev_buffer);
  free (file->dwarf_info_buffer);
  free (file->dwarf_addr_buffer);
  free (file->dwarf_str_offsets_buffer);
}

static void
cleanup_comp_unit_tables(struct comp_unit *each, struct dwarf2_debug_file *file)
{
  if (each->line_table && each->line_table != file->line_table)
    {
      free (each->line_table->files);
      free (each->line_table->dirs);
    }

  free (each->lookup_funcinfo_table);
  each->lookup_funcinfo_table = NULL;
}

static void
cleanup_function_table(struct funcinfo *function_table)
{
  while (function_table)
    {
      free (function_table->file);
      function_table->file = NULL;
      free (function_table->caller_file);
      function_table->caller_file = NULL;
      function_table = function_table->prev_func;
    }
}

static void
cleanup_variable_table(struct varinfo *variable_table)
{
  while (variable_table)
    {
      free (variable_table->file);
      variable_table->file = NULL;
      variable_table = variable_table->prev_var;
    }
}

typedef struct elf_find_function_cache
{
  asection *     last_section;
  asymbol *      func;
  const char *   filename;
  bfd_size_type  code_size;
  bfd_vma        code_off;

} elf_find_function_cache;


/* Returns TRUE if symbol SYM with address CODE_OFF and size CODE_SIZE
   is a better fit to match OFFSET than whatever is currenly stored in
   CACHE.  */

static inline bool
better_fit (elf_find_function_cache *cache,
            asymbol *sym,
            bfd_vma code_off,
            bfd_size_type code_size,
            bfd_vma offset)
{
  if (cache == NULL || sym == NULL)
    return false;

  if (code_off > offset)
    return false;

  if (code_off < cache->code_off)
    return false;

  if (code_off > cache->code_off)
    return true;

  if (cache->code_off + cache->code_size <= offset)
    return code_size > cache->code_size;

  if (code_off + code_size <= offset)
    return false;

  flagword cache_flags = cache->func->flags;
  flagword sym_flags = sym->flags;
  bool cache_is_function = (cache_flags & BSF_FUNCTION) != 0;
  bool sym_is_function = (sym_flags & BSF_FUNCTION) != 0;

  if (cache_is_function && !sym_is_function)
    return false;
  
  if (sym_is_function && !cache_is_function)
    return true;

  elf_symbol_type *cache_elf = (elf_symbol_type *) cache->func;
  elf_symbol_type *sym_elf = (elf_symbol_type *) sym;
  
  int cache_type = ELF_ST_TYPE(cache_elf->internal_elf_sym.st_info);
  int sym_type = ELF_ST_TYPE(sym_elf->internal_elf_sym.st_info);

  if (cache_type == STT_NOTYPE && sym_type != STT_NOTYPE)
    return true;
  
  if (cache_type != STT_NOTYPE && sym_type == STT_NOTYPE)
    return false;

  return code_size < cache->code_size;
}

/* Find the function to a particular section and offset,
   for error reporting.  */

asymbol *
_bfd_elf_find_function (bfd *abfd,
			asymbol **symbols,
			asection *section,
			bfd_vma offset,
			const char **filename_ptr,
			const char **functionname_ptr)
{
  if (symbols == NULL || abfd == NULL || section == NULL)
    return NULL;

  if (bfd_get_flavour (abfd) != bfd_target_elf_flavour)
    return NULL;

  elf_find_function_cache *cache = elf_tdata (abfd)->elf_find_function_cache;

  if (cache == NULL)
    {
      cache = bfd_zalloc (abfd, sizeof (*cache));
      if (cache == NULL)
	return NULL;
      elf_tdata (abfd)->elf_find_function_cache = cache;
    }

  if (cache->last_section != section
      || cache->func == NULL
      || offset < cache->func->value
      || offset >= cache->func->value + cache->code_size)
    {
      if (!update_cache_for_section (abfd, symbols, section, offset, cache))
	return NULL;
    }

  if (cache->func == NULL)
    return NULL;

  if (filename_ptr != NULL)
    *filename_ptr = cache->filename;
  if (functionname_ptr != NULL)
    *functionname_ptr = bfd_asymbol_name (cache->func);

  return cache->func;
}

static bool
update_cache_for_section (bfd *abfd,
			  asymbol **symbols,
			  asection *section,
			  bfd_vma offset,
			  elf_find_function_cache *cache)
{
  typedef enum { nothing_seen, symbol_seen, file_after_symbol_seen } state_t;
  
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  asymbol *file = NULL;
  state_t state = nothing_seen;
  
  cache->filename = NULL;
  cache->func = NULL;
  cache->code_size = 0;
  cache->code_off = 0;
  cache->last_section = section;

  for (asymbol **p = symbols; *p != NULL; p++)
    {
      asymbol *sym = *p;
      
      if ((sym->flags & BSF_FILE) != 0)
	{
	  file = sym;
	  if (state == symbol_seen)
	    state = file_after_symbol_seen;
	  continue;
	}

      if (state == nothing_seen)
	state = symbol_seen;

      bfd_vma code_off;
      bfd_size_type size = bed->maybe_function_sym (sym, section, &code_off);

      if (size == 0)
	continue;

      process_symbol (cache, sym, code_off, size, offset, file, state);
    }
  
  return true;
}

static void
process_symbol (elf_find_function_cache *cache,
		asymbol *sym,
		bfd_vma code_off,
		bfd_size_type size,
		bfd_vma offset,
		asymbol *file,
		int state)
{
  if (better_fit (cache, sym, code_off, size, offset))
    {
      cache->func = sym;
      cache->code_size = size;
      cache->code_off = code_off;
      cache->filename = NULL;

      if (file != NULL
	  && ((sym->flags & BSF_LOCAL) != 0
	      || state != 2))
	cache->filename = bfd_asymbol_name (file);
    }
  else if (code_off > offset 
	   && code_off > cache->code_off
	   && code_off < cache->code_off + cache->code_size)
    {
      cache->code_size = code_off - cache->code_off;
    }
}
