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

static struct trie_node *alloc_trie_leaf (bfd *abfd)
{
  struct trie_leaf *leaf;
  size_t amt = sizeof (*leaf) + TRIE_LEAF_SIZE * sizeof (leaf->ranges[0]);
  leaf = bfd_zalloc (abfd, amt);
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

static bool
addr_range_intersects (struct addr_range *r1, struct addr_range *r2)
{
  return (r1->start <= r2->start && r2->start < r1->end)
    || (r1->start <= (r2->end - 1) && (r2->end - 1) < r1->end);
}

/* Compare function for splay tree of addr_ranges.  */

static int
splay_tree_compare_addr_range (splay_tree_key xa, splay_tree_key xb)
{
  struct addr_range *r1 = (struct addr_range *) xa;
  struct addr_range *r2 = (struct addr_range *) xb;

  if (addr_range_intersects (r1, r2) || addr_range_intersects (r2, r1))
    return 0;
  
  return (r1->end <= r2->start) ? -1 : 1;
}

/* Splay tree release function for keys (addr_range).  */

static void splay_tree_free_addr_range(splay_tree_key key)
{
    free((struct addr_range *)key);
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
							  sizeof (* ret));
      if (ret == NULL)
	return NULL;
    }

  ret = ((struct info_hash_entry *)
	 bfd_hash_newfunc ((struct bfd_hash_entry *) ret, table, string));

  if (ret)
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

  hash_table = ((struct info_hash_table *)
		bfd_alloc (abfd, sizeof (struct info_hash_table)));
  if (!hash_table)
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
  struct info_hash_entry *entry;
  struct info_list_node *node;

  entry = (struct info_hash_entry*) bfd_hash_lookup (&hash_table->base,
						     key, true, copy_p);
  if (!entry)
    return false;

  node = (struct info_list_node *) bfd_hash_allocate (&hash_table->base,
						      sizeof (*node));
  if (!node)
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

  entry = (struct info_hash_entry*) bfd_hash_lookup (&hash_table->base, key,
						     false, false);
  return entry ? entry->head : NULL;
}

/* Read a section into its appropriate place in the dwarf2_debug
   struct (indicated by SECTION_BUFFER and SECTION_SIZE).  If SYMS is
   not NULL, use bfd_simple_get_relocated_section_contents to read the
   section contents, otherwise use bfd_get_section_contents.  Fail if
   the located section does not contain at least OFFSET bytes.  */

static asection *
find_section(bfd *abfd, const struct dwarf_debug_section *sec, const char **section_name)
{
  asection *msec = bfd_get_section_by_name(abfd, sec->uncompressed_name);
  *section_name = sec->uncompressed_name;
  
  if (msec == NULL)
    {
      *section_name = sec->compressed_name;
      msec = bfd_get_section_by_name(abfd, *section_name);
    }
  
  return msec;
}

static bool
validate_section(asection *msec, const char *section_name, bfd *abfd)
{
  if (msec == NULL)
    {
      _bfd_error_handler(_("DWARF error: can't find %s section."), section_name);
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  if ((msec->flags & SEC_HAS_CONTENTS) == 0)
    {
      _bfd_error_handler(_("DWARF error: section %s has no contents"), section_name);
      bfd_set_error(bfd_error_no_contents);
      return false;
    }

  if (bfd_section_size_insane(abfd, msec))
    {
      _bfd_error_handler(_("DWARF error: section %s is too big"), section_name);
      return false;
    }

  return true;
}

static bfd_byte *
allocate_section_buffer(bfd_size_type amt)
{
  amt += 1;
  if (amt == 0)
    {
      bfd_set_error(bfd_error_no_memory);
      return NULL;
    }
  return (bfd_byte *) bfd_malloc(amt);
}

static bool
load_section_contents(bfd *abfd, asection *msec, bfd_byte *contents, 
                     bfd_size_type section_size, asymbol **syms)
{
  if (syms)
    return bfd_simple_get_relocated_section_contents(abfd, msec, contents, syms);
  else
    return bfd_get_section_contents(abfd, msec, contents, 0, section_size);
}

static bool
validate_offset(uint64_t offset, bfd_size_type section_size, const char *section_name)
{
  if (offset != 0 && offset >= section_size)
    {
      _bfd_error_handler(_("DWARF error: offset (%" PRIu64 ")"
                          " greater than or equal to %s size (%" PRIu64 ")"),
                        (uint64_t) offset, section_name,
                        (uint64_t) section_size);
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
read_section(bfd *abfd,
            const struct dwarf_debug_section *sec,
            asymbol **syms,
            uint64_t offset,
            bfd_byte **section_buffer,
            bfd_size_type *section_size)
{
  bfd_byte *contents = *section_buffer;

  if (contents == NULL)
    {
      const char *section_name;
      asection *msec = find_section(abfd, sec, &section_name);
      
      if (!validate_section(msec, sec->uncompressed_name, abfd))
        return false;

      bfd_size_type amt = bfd_get_section_limit_octets(abfd, msec);
      *section_size = amt;
      
      contents = allocate_section_buffer(amt);
      if (contents == NULL)
        return false;

      if (!load_section_contents(abfd, msec, contents, *section_size, syms))
        {
          free(contents);
          return false;
        }
      
      contents[*section_size] = 0;
      *section_buffer = contents;
    }

  return validate_offset(offset, *section_size, 
                         sec->uncompressed_name);
}

/* Read dwarf information from a buffer.  */

static inline uint64_t
read_n_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end, int n)
{
  bfd_byte *buf = *ptr;
  if (end - buf < n)
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
  const int SINGLE_BYTE = 1;
  return read_n_bytes (abfd, ptr, end, SINGLE_BYTE);
}

static int
read_1_signed_byte (bfd *abfd ATTRIBUTE_UNUSED, bfd_byte **ptr, bfd_byte *end)
{
  bfd_byte *buf = *ptr;
  if (end - buf < 1)
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
  const int BYTES_TO_READ = 4;
  return read_n_bytes (abfd, ptr, end, BYTES_TO_READ);
}

static uint64_t
read_8_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  const int EIGHT_BYTES = 8;
  return read_n_bytes (abfd, ptr, end, EIGHT_BYTES);
}

static struct dwarf_block *
allocate_block (bfd *abfd)
{
  return (struct dwarf_block *) bfd_alloc (abfd, sizeof (struct dwarf_block));
}

static void
initialize_empty_block (struct dwarf_block *block)
{
  block->data = NULL;
  block->size = 0;
}

static void
initialize_block_with_data (struct dwarf_block *block, bfd_byte *buf, size_t size)
{
  block->data = buf;
  block->size = size;
}

static struct dwarf_block *
read_blk (bfd *abfd, bfd_byte **ptr, bfd_byte *end, size_t size)
{
  bfd_byte *buf = *ptr;
  struct dwarf_block *block;

  block = allocate_block (abfd);
  if (block == NULL)
    return NULL;

  if (size > (size_t) (end - buf))
    {
      *ptr = end;
      initialize_empty_block (block);
    }
  else
    {
      *ptr = buf + size;
      initialize_block_with_data (block, buf, size);
    }
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
  bfd_byte *buf = *ptr;
  bfd_byte *str = buf;

  while (buf < buf_end && *buf != 0)
    {
      buf++;
    }

  if (buf >= buf_end || str == buf)
    {
      *ptr = buf;
      return NULL;
    }

  buf++;
  *ptr = buf;
  return (char *) str;
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
  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  uint64_t offset = read_offset_by_size(unit, ptr, buf_end);
  
  return fetch_string_at_offset(unit, offset);
}

static uint64_t
read_offset_by_size (struct comp_unit *unit,
                     bfd_byte **ptr,
                     bfd_byte *buf_end)
{
  const int OFFSET_SIZE_32 = 4;
  
  if (unit->offset_size == OFFSET_SIZE_32)
    return read_4_bytes (unit->abfd, ptr, buf_end);
  
  return read_8_bytes (unit->abfd, ptr, buf_end);
}

static char *
fetch_string_at_offset (struct comp_unit *unit,
                        uint64_t offset)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  
  if (! read_section (unit->abfd, &stash->debug_sections[debug_str],
		      file->syms, offset,
		      &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  char *str = (char *) file->dwarf_str_buffer + offset;
  
  if (*str == '\0')
    return NULL;
    
  return str;
}

/* Like read_indirect_string but from .debug_line_str section.  */

static uint64_t read_offset_by_size(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
    if (unit->offset_size == 4)
        return read_4_bytes(unit->abfd, ptr, buf_end);
    return read_8_bytes(unit->abfd, ptr, buf_end);
}

static bool is_offset_size_valid(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
    if (unit->offset_size > (size_t)(buf_end - *ptr))
    {
        *ptr = buf_end;
        return false;
    }
    return true;
}

static char *get_string_from_buffer(struct dwarf2_debug_file *file, uint64_t offset)
{
    char *str = (char *)file->dwarf_line_str_buffer + offset;
    if (*str == '\0')
        return NULL;
    return str;
}

static char *read_indirect_line_string(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
    if (!is_offset_size_valid(unit, ptr, buf_end))
        return NULL;

    uint64_t offset = read_offset_by_size(unit, ptr, buf_end);
    
    struct dwarf2_debug *stash = unit->stash;
    struct dwarf2_debug_file *file = unit->file;

    if (!read_section(unit->abfd, &stash->debug_sections[debug_line_str],
                      file->syms, offset,
                      &file->dwarf_line_str_buffer,
                      &file->dwarf_line_str_size))
        return NULL;

    return get_string_from_buffer(file, offset);
}

/* Like read_indirect_string but uses a .debug_str located in
   an alternate file pointed to by the .gnu_debugaltlink section.
   Used to impement DW_FORM_GNU_strp_alt.  */

static uint64_t read_offset_by_size(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
    if (unit->offset_size == 4)
        return read_4_bytes(unit->abfd, ptr, buf_end);
    return read_8_bytes(unit->abfd, ptr, buf_end);
}

static bfd *open_debug_alt_file(bfd *abfd)
{
    char *debug_filename = bfd_follow_gnu_debugaltlink(abfd, DEBUGDIR);
    if (debug_filename == NULL)
        return NULL;

    bfd *debug_bfd = bfd_openr(debug_filename, NULL);
    free(debug_filename);
    
    if (debug_bfd == NULL)
        return NULL;

    if (!bfd_check_format(debug_bfd, bfd_object))
    {
        bfd_close(debug_bfd);
        return NULL;
    }
    
    return debug_bfd;
}

static int ensure_alt_bfd_loaded(struct comp_unit *unit)
{
    struct dwarf2_debug *stash = unit->stash;
    
    if (stash->alt.bfd_ptr != NULL)
        return 1;
    
    stash->alt.bfd_ptr = open_debug_alt_file(unit->abfd);
    return stash->alt.bfd_ptr != NULL;
}

static char *get_string_from_offset(struct dwarf2_debug *stash, uint64_t offset)
{
    if (!read_section(stash->alt.bfd_ptr,
                     stash->debug_sections + debug_str_alt,
                     stash->alt.syms, offset,
                     &stash->alt.dwarf_str_buffer,
                     &stash->alt.dwarf_str_size))
        return NULL;

    char *str = (char *) stash->alt.dwarf_str_buffer + offset;
    if (*str == '\0')
        return NULL;

    return str;
}

static char *read_alt_indirect_string(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
    if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
        *ptr = buf_end;
        return NULL;
    }

    uint64_t offset = read_offset_by_size(unit, ptr, buf_end);
    
    if (!ensure_alt_bfd_loaded(unit))
        return NULL;

    return get_string_from_offset(unit->stash, offset);
}

/* Resolve an alternate reference from UNIT at OFFSET.
   Returns a pointer into the loaded alternate CU upon success
   or NULL upon failure.  */

static bfd *open_debug_bfd(bfd *abfd)
{
    char *debug_filename = bfd_follow_gnu_debugaltlink(abfd, DEBUGDIR);
    if (debug_filename == NULL)
        return NULL;

    bfd *debug_bfd = bfd_openr(debug_filename, NULL);
    free(debug_filename);
    
    if (debug_bfd == NULL)
        return NULL;

    if (!bfd_check_format(debug_bfd, bfd_object))
    {
        bfd_close(debug_bfd);
        return NULL;
    }
    
    return debug_bfd;
}

static bfd *get_or_open_alt_bfd(struct comp_unit *unit)
{
    struct dwarf2_debug *stash = unit->stash;
    
    if (stash->alt.bfd_ptr != NULL)
        return stash->alt.bfd_ptr;
    
    bfd *debug_bfd = open_debug_bfd(unit->abfd);
    if (debug_bfd == NULL)
        return NULL;
    
    stash->alt.bfd_ptr = debug_bfd;
    return debug_bfd;
}

static bfd_byte *
read_alt_indirect_ref (struct comp_unit *unit, uint64_t offset)
{
    struct dwarf2_debug *stash = unit->stash;
    
    if (get_or_open_alt_bfd(unit) == NULL)
        return NULL;

    if (!read_section(stash->alt.bfd_ptr,
                      stash->debug_sections + debug_info_alt,
                      stash->alt.syms, offset,
                      &stash->alt.dwarf_info_buffer,
                      &stash->alt.dwarf_info_size))
        return NULL;

    return stash->alt.dwarf_info_buffer + offset;
}

static int
is_signed_vma_enabled(struct comp_unit *unit)
{
  if (bfd_get_flavour(unit->abfd) == bfd_target_elf_flavour)
    return get_elf_backend_data(unit->abfd)->sign_extend_vma;
  return 0;
}

static int
has_sufficient_buffer_space(struct comp_unit *unit, bfd_byte *buf, bfd_byte *buf_end)
{
  return unit->addr_size <= (size_t)(buf_end - buf);
}

static uint64_t
read_signed_value(struct comp_unit *unit, bfd_byte *buf)
{
  switch (unit->addr_size)
    {
    case 8:
      return bfd_get_signed_64(unit->abfd, buf);
    case 4:
      return bfd_get_signed_32(unit->abfd, buf);
    case 2:
      return bfd_get_signed_16(unit->abfd, buf);
    default:
      abort();
    }
}

static uint64_t
read_unsigned_value(struct comp_unit *unit, bfd_byte *buf)
{
  switch (unit->addr_size)
    {
    case 8:
      return bfd_get_64(unit->abfd, buf);
    case 4:
      return bfd_get_32(unit->abfd, buf);
    case 2:
      return bfd_get_16(unit->abfd, buf);
    default:
      abort();
    }
}

static uint64_t
read_address(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
  bfd_byte *buf = *ptr;

  if (!has_sufficient_buffer_space(unit, buf, buf_end))
    {
      *ptr = buf_end;
      return 0;
    }

  *ptr = buf + unit->addr_size;
  
  if (is_signed_vma_enabled(unit))
    return read_signed_value(unit, buf);
  
  return read_unsigned_value(unit, buf);
}

/* Lookup an abbrev_info structure in the abbrev hash table.  */

static struct abbrev_info *
lookup_abbrev (unsigned int number, struct abbrev_info **abbrevs)
{
  unsigned int hash_number;
  struct abbrev_info *abbrev;

  hash_number = number % ABBREV_HASH_SIZE;
  abbrev = abbrevs[hash_number];

  while (abbrev)
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
hash_abbrev(const void *p)
{
    const struct abbrev_offset_entry *ent = p;
    return htab_hash_pointer((void *)ent->offset);
}

static int
eq_abbrev (const void *pa, const void *pb)
{
  const struct abbrev_offset_entry *a = pa;
  const struct abbrev_offset_entry *b = pb;
  return a->offset == b->offset;
}

static void free_abbrev_list(struct abbrev_info *abbrev)
{
    while (abbrev)
    {
        free(abbrev->attrs);
        abbrev = abbrev->next;
    }
}

static void free_all_abbrevs(struct abbrev_info **abbrevs)
{
    size_t i;
    for (i = 0; i < ABBREV_HASH_SIZE; i++)
    {
        free_abbrev_list(abbrevs[i]);
    }
}

static void del_abbrev(void *p)
{
    struct abbrev_offset_entry *ent = p;
    free_all_abbrevs(ent->abbrevs);
    free(ent);
}

/* In DWARF version 2, the description of the debugging information is
   stored in a separate .debug_abbrev section.  Before we read any
   dies from a section we read in all abbreviations and install them
   in a hash table.  */

static struct abbrev_info** find_existing_abbrevs(void **slot, uint64_t offset)
{
  if (slot == NULL)
    return NULL;
  if (*slot != NULL)
    return ((struct abbrev_offset_entry *) (*slot))->abbrevs;
  return NULL;
}

static struct abbrev_info** allocate_abbrevs_table(bfd *abfd)
{
  size_t amt = sizeof (struct abbrev_info*) * ABBREV_HASH_SIZE;
  return (struct abbrev_info **) bfd_zalloc (abfd, amt);
}

static struct abbrev_info* allocate_abbrev_info(bfd *abfd)
{
  size_t amt = sizeof (struct abbrev_info);
  return (struct abbrev_info *) bfd_zalloc (abfd, amt);
}

static bool read_abbrev_header(struct abbrev_info *cur_abbrev, 
                               bfd *abfd, bfd_byte **abbrev_ptr, 
                               bfd_byte *abbrev_end, unsigned int abbrev_number)
{
  cur_abbrev->number = abbrev_number;
  cur_abbrev->tag = (enum dwarf_tag)
    _bfd_safe_read_leb128 (abfd, abbrev_ptr, false, abbrev_end);
  cur_abbrev->has_children = read_1_byte (abfd, abbrev_ptr, abbrev_end);
  return true;
}

static struct attr_abbrev* expand_attrs_array(struct abbrev_info *cur_abbrev)
{
  size_t amt = cur_abbrev->num_attrs + ATTR_ALLOC_CHUNK;
  amt *= sizeof (struct attr_abbrev);
  return (struct attr_abbrev *) bfd_realloc (cur_abbrev->attrs, amt);
}

static bool read_attribute_declaration(struct abbrev_info *cur_abbrev,
                                      bfd *abfd, bfd_byte **abbrev_ptr,
                                      bfd_byte *abbrev_end)
{
  bfd_vma implicit_const = -1;
  
  unsigned int abbrev_name = _bfd_safe_read_leb128 (abfd, abbrev_ptr,
                                                    false, abbrev_end);
  unsigned int abbrev_form = _bfd_safe_read_leb128 (abfd, abbrev_ptr,
                                                    false, abbrev_end);
  
  if (abbrev_form == DW_FORM_implicit_const)
    implicit_const = _bfd_safe_read_leb128 (abfd, abbrev_ptr, true, abbrev_end);
  
  if (abbrev_name == 0)
    return false;
  
  if ((cur_abbrev->num_attrs % ATTR_ALLOC_CHUNK) == 0)
    {
      struct attr_abbrev *tmp = expand_attrs_array(cur_abbrev);
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

static bool read_abbrev_declarations(struct abbrev_info *cur_abbrev,
                                    bfd *abfd, bfd_byte **abbrev_ptr,
                                    bfd_byte *abbrev_end)
{
  for (;;)
    {
      if (!read_attribute_declaration(cur_abbrev, abfd, abbrev_ptr, abbrev_end))
        break;
    }
  return true;
}

static void add_abbrev_to_hash(struct abbrev_info *cur_abbrev, 
                               struct abbrev_info **abbrevs,
                               unsigned int abbrev_number)
{
  unsigned int hash_number = abbrev_number % ABBREV_HASH_SIZE;
  cur_abbrev->next = abbrevs[hash_number];
  abbrevs[hash_number] = cur_abbrev;
}

static bool should_continue_reading(bfd_byte *abbrev_ptr, 
                                   struct dwarf2_debug_file *file,
                                   unsigned int abbrev_number,
                                   struct abbrev_info **abbrevs)
{
  if ((size_t) (abbrev_ptr - file->dwarf_abbrev_buffer) >= file->dwarf_abbrev_size)
    return false;
  if (abbrev_number == 0)
    return false;
  if (lookup_abbrev (abbrev_number, abbrevs) != NULL)
    return false;
  return true;
}

static void free_abbrev_chain(struct abbrev_info *abbrev)
{
  while (abbrev)
    {
      free (abbrev->attrs);
      abbrev = abbrev->next;
    }
}

static void cleanup_abbrevs(struct abbrev_info **abbrevs)
{
  if (abbrevs != NULL)
    {
      size_t i;
      for (i = 0; i < ABBREV_HASH_SIZE; i++)
        free_abbrev_chain(abbrevs[i]);
      free (abbrevs);
    }
}

static bool save_abbrevs_to_slot(void **slot, struct abbrev_info **abbrevs, 
                                 uint64_t offset)
{
  struct abbrev_offset_entry ent = { offset, abbrevs };
  *slot = bfd_malloc (sizeof ent);
  if (!*slot)
    return false;
  memcpy (*slot, &ent, sizeof ent);
  return true;
}

static struct abbrev_info* read_single_abbrev(bfd *abfd, bfd_byte **abbrev_ptr,
                                              bfd_byte *abbrev_end,
                                              unsigned int abbrev_number)
{
  struct abbrev_info *cur_abbrev = allocate_abbrev_info(abfd);
  if (cur_abbrev == NULL)
    return NULL;
  
  read_abbrev_header(cur_abbrev, abfd, abbrev_ptr, abbrev_end, abbrev_number);
  
  if (!read_abbrev_declarations(cur_abbrev, abfd, abbrev_ptr, abbrev_end))
    return cur_abbrev;
  
  return cur_abbrev;
}

static struct abbrev_info**
read_abbrevs (bfd *abfd, uint64_t offset, struct dwarf2_debug *stash,
	      struct dwarf2_debug_file *file)
{
  struct abbrev_info **abbrevs;
  bfd_byte *abbrev_ptr;
  bfd_byte *abbrev_end;
  struct abbrev_info *cur_abbrev;
  unsigned int abbrev_number;
  void **slot;
  struct abbrev_offset_entry ent = { offset, NULL };

  if (ent.offset != offset)
    return NULL;

  slot = htab_find_slot (file->abbrev_offsets, &ent, INSERT);
  
  struct abbrev_info **existing = find_existing_abbrevs(slot, offset);
  if (existing != NULL)
    return existing;

  if (! read_section (abfd, &stash->debug_sections[debug_abbrev],
		      file->syms, offset,
		      &file->dwarf_abbrev_buffer,
		      &file->dwarf_abbrev_size))
    return NULL;

  abbrevs = allocate_abbrevs_table(abfd);
  if (abbrevs == NULL)
    return NULL;

  abbrev_ptr = file->dwarf_abbrev_buffer + offset;
  abbrev_end = file->dwarf_abbrev_buffer + file->dwarf_abbrev_size;
  abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);

  while (abbrev_number)
    {
      cur_abbrev = read_single_abbrev(abfd, &abbrev_ptr, abbrev_end, abbrev_number);
      if (cur_abbrev == NULL)
        goto fail;
      
      add_abbrev_to_hash(cur_abbrev, abbrevs, abbrev_number);
      
      if (!should_continue_reading(abbrev_ptr, file, abbrev_number, abbrevs))
        break;
      
      abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
    }

  if (!save_abbrevs_to_slot(slot, abbrevs, offset))
    goto fail;
  
  return abbrevs;

 fail:
  cleanup_abbrevs(abbrevs);
  return NULL;
}

/* Returns true if the form is one which has a string value.  */

static bool
is_str_form (const struct attribute *attr)
{
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
  return (form == DW_FORM_strx
	  || form == DW_FORM_strx1
	  || form == DW_FORM_strx2
	  || form == DW_FORM_strx3
	  || form == DW_FORM_strx4);
}

/* Return true if the form is addrx[1-4].  */

static inline bool
is_addrx_form (enum dwarf_form form)
{
  return (form == DW_FORM_addrx
	  || form == DW_FORM_addrx1
	  || form == DW_FORM_addrx2
	  || form == DW_FORM_addrx3
	  || form == DW_FORM_addrx4);
}

/* Returns the address in .debug_addr section using DW_AT_addr_base.
   Used to implement DW_FORM_addrx*.  */
static uint64_t
read_indexed_address (uint64_t idx, struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  bfd_byte *info_ptr;
  size_t offset;

  if (stash == NULL)
    return 0;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_addr],
		     file->syms, 0,
		     &file->dwarf_addr_buffer, &file->dwarf_addr_size))
    return 0;

  if (_bfd_mul_overflow (idx, unit->addr_size, &offset))
    return 0;

  offset += unit->dwarf_addr_offset;
  if (!is_valid_offset(offset, unit, file))
    return 0;

  info_ptr = file->dwarf_addr_buffer + offset;
  return read_address_by_size(unit, info_ptr);
}

static int
is_valid_offset(size_t offset, struct comp_unit *unit, struct dwarf2_debug_file *file)
{
  return offset >= unit->dwarf_addr_offset
         && offset <= file->dwarf_addr_size
         && file->dwarf_addr_size - offset >= unit->addr_size;
}

static uint64_t
read_address_by_size(struct comp_unit *unit, bfd_byte *info_ptr)
{
  #define ADDR_SIZE_32 4
  #define ADDR_SIZE_64 8
  
  if (unit->addr_size == ADDR_SIZE_32)
    return bfd_get_32 (unit->abfd, info_ptr);
  if (unit->addr_size == ADDR_SIZE_64)
    return bfd_get_64 (unit->abfd, info_ptr);
  return 0;
}

/* Returns the string using DW_AT_str_offsets_base.
   Used to implement DW_FORM_strx*.  */
static const char *
read_indexed_string (uint64_t idx, struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  
  if (stash == NULL)
    return NULL;

  if (!load_string_sections(unit, stash, file))
    return NULL;

  size_t offset;
  if (!calculate_string_offset(idx, unit, &offset))
    return NULL;

  if (!validate_offset_bounds(offset, unit, file))
    return NULL;

  uint64_t str_offset;
  if (!read_string_offset(unit, file, offset, &str_offset))
    return NULL;

  if (str_offset >= file->dwarf_str_size)
    return NULL;
    
  return (const char *) file->dwarf_str_buffer + str_offset;
}

static bool
load_string_sections(struct comp_unit *unit, struct dwarf2_debug *stash, 
                     struct dwarf2_debug_file *file)
{
  if (!read_section(unit->abfd, &stash->debug_sections[debug_str],
                    file->syms, 0,
                    &file->dwarf_str_buffer, &file->dwarf_str_size))
    return false;

  if (!read_section(unit->abfd, &stash->debug_sections[debug_str_offsets],
                    file->syms, 0,
                    &file->dwarf_str_offsets_buffer,
                    &file->dwarf_str_offsets_size))
    return false;

  return true;
}

static bool
calculate_string_offset(uint64_t idx, struct comp_unit *unit, size_t *offset)
{
  if (_bfd_mul_overflow(idx, unit->offset_size, offset))
    return false;

  *offset += unit->dwarf_str_offset;
  return true;
}

static bool
validate_offset_bounds(size_t offset, struct comp_unit *unit, 
                      struct dwarf2_debug_file *file)
{
  if (offset < unit->dwarf_str_offset)
    return false;
    
  if (offset > file->dwarf_str_offsets_size)
    return false;
    
  if (file->dwarf_str_offsets_size - offset < unit->offset_size)
    return false;
    
  return true;
}

static bool
read_string_offset(struct comp_unit *unit, struct dwarf2_debug_file *file,
                  size_t offset, uint64_t *str_offset)
{
  bfd_byte *info_ptr = file->dwarf_str_offsets_buffer + offset;

  if (unit->offset_size == 4)
    *str_offset = bfd_get_32(unit->abfd, info_ptr);
  else if (unit->offset_size == 8)
    *str_offset = bfd_get_64(unit->abfd, info_ptr);
  else
    return false;

  return true;
}

/* Read and fill in the value of attribute ATTR as described by FORM.
   Read data starting from INFO_PTR, but never at or beyond INFO_PTR_END.
   Returns an updated INFO_PTR taking into account the amount of data read.  */

static bfd_byte *
read_bytes_by_unit_offset(struct comp_unit *unit, bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end)
{
  if (unit->offset_size == 4)
    return read_4_bytes(abfd, info_ptr, info_ptr_end);
  else
    return read_8_bytes(abfd, info_ptr, info_ptr_end);
}

static void
read_indexed_address_if_offset_set(struct attribute *attr, struct comp_unit *unit)
{
  if (unit->dwarf_addr_offset != 0)
    attr->u.val = read_indexed_address(attr->u.val, unit);
}

static void
read_indexed_string_if_offset_set(struct attribute *attr, struct comp_unit *unit)
{
  if (unit->dwarf_str_offset != 0)
    attr->u.str = (char *)read_indexed_string(attr->u.val, unit);
  else
    attr->u.str = NULL;
}

static bfd_byte *
read_block_attribute(struct attribute *attr, bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end, size_t amt)
{
  attr->u.blk = read_blk(abfd, info_ptr, info_ptr_end, amt);
  if (attr->u.blk == NULL)
    return NULL;
  return *info_ptr;
}

static bfd_byte *
process_addrx_form(struct attribute *attr, bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end, 
                   struct comp_unit *unit, int byte_count)
{
  if (byte_count == 1)
    attr->u.val = read_1_byte(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 2)
    attr->u.val = read_2_bytes(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 3)
    attr->u.val = read_3_bytes(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 4)
    attr->u.val = read_4_bytes(abfd, info_ptr, info_ptr_end);
  
  read_indexed_address_if_offset_set(attr, unit);
  return *info_ptr;
}

static bfd_byte *
process_strx_form(struct attribute *attr, bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end,
                  struct comp_unit *unit, int byte_count)
{
  if (byte_count == 1)
    attr->u.val = read_1_byte(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 2)
    attr->u.val = read_2_bytes(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 3)
    attr->u.val = read_3_bytes(abfd, info_ptr, info_ptr_end);
  else if (byte_count == 4)
    attr->u.val = read_4_bytes(abfd, info_ptr, info_ptr_end);
  
  read_indexed_string_if_offset_set(attr, unit);
  return *info_ptr;
}

static bfd_byte *
read_attribute_value(struct attribute *attr, unsigned form, bfd_vma implicit_const,
                    struct comp_unit *unit, bfd_byte *info_ptr, bfd_byte *info_ptr_end)
{
  bfd *abfd = unit->abfd;
  size_t amt;

  if (info_ptr >= info_ptr_end && form != DW_FORM_flag_present)
    {
      _bfd_error_handler(_("DWARF error: info pointer extends beyond end of attributes"));
      bfd_set_error(bfd_error_bad_value);
      return NULL;
    }

  attr->form = (enum dwarf_form)form;

  switch (form)
    {
    case DW_FORM_flag_present:
      attr->u.val = 1;
      break;
    case DW_FORM_ref_addr:
      if (unit->version >= 3)
        {
          attr->u.val = read_bytes_by_unit_offset(unit, abfd, &info_ptr, info_ptr_end);
          break;
        }
    case DW_FORM_addr:
      attr->u.val = read_address(unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_GNU_ref_alt:
    case DW_FORM_sec_offset:
      attr->u.val = read_bytes_by_unit_offset(unit, abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_block2:
      amt = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      return read_block_attribute(attr, abfd, &info_ptr, info_ptr_end, amt);
    case DW_FORM_block4:
      amt = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      return read_block_attribute(attr, abfd, &info_ptr, info_ptr_end, amt);
    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      attr->u.val = read_1_byte(abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx1:
      return process_addrx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 1);
    case DW_FORM_data2:
    case DW_FORM_ref2:
      attr->u.val = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx2:
      return process_addrx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 2);
    case DW_FORM_addrx3:
      return process_addrx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 3);
    case DW_FORM_ref4:
    case DW_FORM_data4:
      attr->u.val = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_addrx4:
      return process_addrx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 4);
    case DW_FORM_data8:
    case DW_FORM_ref8:
    case DW_FORM_ref_sig8:
      attr->u.val = read_8_bytes(abfd, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_string:
      attr->u.str = read_string(&info_ptr, info_ptr_end);
      break;
    case DW_FORM_strp:
      attr->u.str = read_indirect_string(unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_line_strp:
      attr->u.str = read_indirect_line_string(unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_GNU_strp_alt:
      attr->u.str = read_alt_indirect_string(unit, &info_ptr, info_ptr_end);
      break;
    case DW_FORM_strx1:
      return process_strx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 1);
    case DW_FORM_strx2:
      return process_strx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 2);
    case DW_FORM_strx3:
      return process_strx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 3);
    case DW_FORM_strx4:
      return process_strx_form(attr, abfd, &info_ptr, info_ptr_end, unit, 4);
    case DW_FORM_strx:
      attr->u.val = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      read_indexed_string_if_offset_set(attr, unit);
      break;
    case DW_FORM_exprloc:
    case DW_FORM_block:
      amt = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      return read_block_attribute(attr, abfd, &info_ptr, info_ptr_end, amt);
    case DW_FORM_block1:
      amt = read_1_byte(abfd, &info_ptr, info_ptr_end);
      return read_block_attribute(attr, abfd, &info_ptr, info_ptr_end, amt);
    case DW_FORM_sdata:
      attr->u.sval = _bfd_safe_read_leb128(abfd, &info_ptr, true, info_ptr_end);
      break;
    case DW_FORM_rnglistx:
    case DW_FORM_loclistx:
    case DW_FORM_ref_udata:
    case DW_FORM_udata:
      attr->u.val = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      break;
    case DW_FORM_addrx:
      attr->u.val = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      read_indexed_address_if_offset_set(attr, unit);
      break;
    case DW_FORM_indirect:
      form = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      if (form == DW_FORM_implicit_const)
        implicit_const = _bfd_safe_read_leb128(abfd, &info_ptr, true, info_ptr_end);
      info_ptr = read_attribute_value(attr, form, implicit_const, unit, info_ptr, info_ptr_end);
      break;
    case DW_FORM_implicit_const:
      attr->form = DW_FORM_sdata;
      attr->u.sval = implicit_const;
      break;
    case DW_FORM_data16:
      return read_block_attribute(attr, abfd, &info_ptr, info_ptr_end, 16);
    default:
      _bfd_error_handler(_("DWARF error: invalid or unhandled FORM value: %#x"), form);
      bfd_set_error(bfd_error_bad_value);
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
  attr->name = abbrev->name;
  info_ptr = read_attribute_value (attr, abbrev->form, abbrev->implicit_const,
				   unit, info_ptr, info_ptr_end);
  return info_ptr;
}

/* Return mangling style given LANG.  */

static int
mangle_style (int lang)
{
  switch (lang)
    {
    case DW_LANG_Ada83:
    case DW_LANG_Ada95:
    case DW_LANG_Ada2005:
    case DW_LANG_Ada2012:
      return DMGL_GNAT;

    case DW_LANG_C_plus_plus:
    case DW_LANG_C_plus_plus_03:
    case DW_LANG_C_plus_plus_11:
    case DW_LANG_C_plus_plus_14:
    case DW_LANG_C_plus_plus_17:
    case DW_LANG_C_plus_plus_20:
    case DW_LANG_C_plus_plus_23:
      return DMGL_GNU_V3;

    case DW_LANG_Java:
      return DMGL_JAVA;

    case DW_LANG_D:
      return DMGL_DLANG;

    case DW_LANG_Rust:
    case DW_LANG_Rust_old:
      return DMGL_RUST;

    case DW_LANG_C89:
    case DW_LANG_C:
    case DW_LANG_Cobol74:
    case DW_LANG_Cobol85:
    case DW_LANG_Fortran77:
    case DW_LANG_Fortran18:
    case DW_LANG_Fortran23:
    case DW_LANG_Pascal83:
    case DW_LANG_PLI:
    case DW_LANG_C99:
    case DW_LANG_UPC:
    case DW_LANG_C11:
    case DW_LANG_C17:
    case DW_LANG_C23:
    case DW_LANG_Mips_Assembler:
    case DW_LANG_Assembly:
    case DW_LANG_Upc:
    case DW_LANG_HP_Basic91:
    case DW_LANG_HP_IMacro:
    case DW_LANG_HP_Assembler:
      return 0;

    default:
      return DMGL_AUTO;
    }
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

static struct line_info* allocate_line_info(bfd *abfd)
{
  size_t amt = sizeof(struct line_info);
  return (struct line_info*) bfd_alloc(abfd, amt);
}

static void initialize_line_info(struct line_info *info, bfd_vma address,
                                 unsigned char op_index, unsigned int line,
                                 unsigned int column, unsigned int discriminator,
                                 int end_sequence)
{
  info->prev_line = NULL;
  info->address = address;
  info->op_index = op_index;
  info->line = line;
  info->column = column;
  info->discriminator = discriminator;
  info->end_sequence = end_sequence;
}

static bool set_filename(struct line_info *info, char *filename, bfd *abfd)
{
  if (filename && filename[0])
    {
      info->filename = (char*) bfd_alloc(abfd, strlen(filename) + 1);
      if (info->filename == NULL)
        return false;
      strcpy(info->filename, filename);
    }
  else
    info->filename = NULL;
  return true;
}

static bool is_duplicate_entry(struct line_sequence *seq, bfd_vma address,
                               unsigned char op_index, int end_sequence)
{
  return seq && seq->last_line->address == address &&
         seq->last_line->op_index == op_index &&
         seq->last_line->end_sequence == end_sequence;
}

static void handle_duplicate_entry(struct line_info_table *table,
                                   struct line_sequence *seq,
                                   struct line_info *info)
{
  if (table->lcl_head == seq->last_line)
    table->lcl_head = info;
  info->prev_line = seq->last_line->prev_line;
  seq->last_line = info;
}

static struct line_sequence* create_new_sequence(bfd_vma address,
                                                 struct line_info_table *table,
                                                 struct line_info *info)
{
  size_t amt = sizeof(struct line_sequence);
  struct line_sequence *seq = (struct line_sequence*) bfd_malloc(amt);
  if (seq == NULL)
    return NULL;
  
  seq->low_pc = address;
  seq->prev_sequence = table->sequences;
  seq->last_line = info;
  table->lcl_head = info;
  table->sequences = seq;
  table->num_sequences++;
  return seq;
}

static void add_to_sequence_normal(struct line_info_table *table,
                                   struct line_sequence *seq,
                                   struct line_info *info)
{
  info->prev_line = seq->last_line;
  seq->last_line = info;
  if (!table->lcl_head)
    table->lcl_head = info;
}

static void insert_after_lcl_head(struct line_info_table *table,
                                  struct line_info *info)
{
  info->prev_line = table->lcl_head->prev_line;
  table->lcl_head->prev_line = info;
}

static struct line_info* find_insertion_point(struct line_sequence *seq,
                                              struct line_info *info)
{
  struct line_info *li2 = seq->last_line;
  struct line_info *li1 = li2->prev_line;
  
  while (li1)
    {
      if (!new_line_sorts_after(info, li2) &&
          new_line_sorts_after(info, li1))
        break;
      li2 = li1;
      li1 = li1->prev_line;
    }
  return li2;
}

static void handle_abnormal_case(struct line_info_table *table,
                                 struct line_sequence *seq,
                                 struct line_info *info)
{
  table->lcl_head = find_insertion_point(seq, info);
  info->prev_line = table->lcl_head->prev_line;
  table->lcl_head->prev_line = info;
  if (info->address < seq->low_pc)
    seq->low_pc = info->address;
}

static bool
add_line_info(struct line_info_table *table,
              bfd_vma address,
              unsigned char op_index,
              char *filename,
              unsigned int line,
              unsigned int column,
              unsigned int discriminator,
              int end_sequence)
{
  struct line_info *info = allocate_line_info(table->abfd);
  if (info == NULL)
    return false;
  
  initialize_line_info(info, address, op_index, line, column,
                      discriminator, end_sequence);
  
  if (!set_filename(info, filename, table->abfd))
    return false;
  
  struct line_sequence *seq = table->sequences;
  
  if (is_duplicate_entry(seq, address, op_index, end_sequence))
    {
      handle_duplicate_entry(table, seq, info);
    }
  else if (!seq || seq->last_line->end_sequence)
    {
      if (create_new_sequence(address, table, info) == NULL)
        return false;
    }
  else if (info->end_sequence || new_line_sorts_after(info, seq->last_line))
    {
      add_to_sequence_normal(table, seq, info);
    }
  else if (!new_line_sorts_after(info, table->lcl_head) &&
           (!table->lcl_head->prev_line ||
            new_line_sorts_after(info, table->lcl_head->prev_line)))
    {
      insert_after_lcl_head(table, info);
    }
  else
    {
      handle_abnormal_case(table, seq, info);
    }
  
  return true;
}

/* Extract a fully qualified filename from a line info table.
   The returned string has been malloc'ed and it is the caller's
   responsibility to free it.  */

static char *strdup_unknown(void)
{
  return strdup("<unknown>");
}

static unsigned int adjust_file_index(struct line_info_table *table, unsigned int file)
{
  if (!table->use_dir_and_file_0)
    {
      if (file == 0)
        return 0;
      return file - 1;
    }
  return file;
}

static unsigned int adjust_dir_index(struct line_info_table *table, unsigned int dir)
{
  if (!table->use_dir_and_file_0)
    return dir - 1;
  return dir;
}

static int validate_file_index(struct line_info_table *table, unsigned int file)
{
  if (table == NULL || file >= table->num_files)
    {
      _bfd_error_handler
        (_("DWARF error: mangled line number section (bad file number)"));
      return 0;
    }
  return 1;
}

static char *get_subdir_name(struct line_info_table *table, unsigned int dir)
{
  if (dir < table->num_dirs)
    return table->dirs[dir];
  return NULL;
}

static void determine_directories(struct line_info_table *table, char *subdir_name, 
                                  char **dir_name, char **subdir_name_out)
{
  if (!subdir_name || !IS_ABSOLUTE_PATH(subdir_name))
    *dir_name = table->comp_dir;

  if (!*dir_name)
    {
      *dir_name = subdir_name;
      *subdir_name_out = NULL;
    }
  else
    {
      *subdir_name_out = subdir_name;
    }
}

static char *build_path_with_subdir(char *dir_name, char *subdir_name, char *filename)
{
  size_t len = strlen(dir_name) + strlen(subdir_name) + strlen(filename) + 3;
  char *name = (char *)bfd_malloc(len);
  if (name)
    sprintf(name, "%s/%s/%s", dir_name, subdir_name, filename);
  return name;
}

static char *build_path_without_subdir(char *dir_name, char *filename)
{
  size_t len = strlen(dir_name) + strlen(filename) + 2;
  char *name = (char *)bfd_malloc(len);
  if (name)
    sprintf(name, "%s/%s", dir_name, filename);
  return name;
}

static char *build_absolute_path(struct line_info_table *table, unsigned int file, char *filename)
{
  char *dir_name = NULL;
  char *subdir_name = NULL;
  unsigned int dir = table->files[file].dir;
  
  dir = adjust_dir_index(table, dir);
  subdir_name = get_subdir_name(table, dir);
  
  determine_directories(table, subdir_name, &dir_name, &subdir_name);
  
  if (!dir_name)
    return strdup(filename);
  
  if (subdir_name)
    return build_path_with_subdir(dir_name, subdir_name, filename);
  
  return build_path_without_subdir(dir_name, filename);
}

static char *concat_filename(struct line_info_table *table, unsigned int file)
{
  char *filename;
  
  file = adjust_file_index(table, file);
  
  if (!table->use_dir_and_file_0 && file == 0)
    return strdup_unknown();
  
  if (!validate_file_index(table, file))
    return strdup_unknown();
  
  filename = table->files[file].name;
  
  if (filename == NULL)
    return strdup_unknown();
  
  if (!IS_ABSOLUTE_PATH(filename))
    return build_absolute_path(table, file, filename);
  
  return strdup(filename);
}

/* Number of bits in a bfd_vma.  */
#define VMA_BITS (8 * sizeof (bfd_vma))

/* Check whether [low1, high1) can be combined with [low2, high2),
   i.e., they touch or overlap.  */

static void swap_ranges(bfd_vma *low1, bfd_vma *high1, bfd_vma *low2, bfd_vma *high2)
{
  bfd_vma tmp;
  
  tmp = *low1;
  *low1 = *low2;
  *low2 = tmp;
  
  tmp = *high1;
  *high1 = *high2;
  *high2 = tmp;
}

static bool ranges_overlap(bfd_vma low1, bfd_vma high1, bfd_vma low2, bfd_vma high2)
{
  if (low1 == low2 || high1 == high2)
    return true;

  if (low1 > low2)
    swap_ranges(&low1, &high1, &low2, &high2);

  return low2 <= high1;
}

/* Insert an address range in the trie mapping addresses to compilation units.
   Will return the new trie node (usually the same as is being sent in, but
   in case of a leaf-to-interior conversion, or expansion of a leaf, it may be
   different), or NULL on failure.  */

static bool try_extend_existing_range(struct trie_leaf *leaf, struct comp_unit *unit,
                                      bfd_vma low_pc, bfd_vma high_pc)
{
    for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
    {
        if (leaf->ranges[i].unit == unit &&
            ranges_overlap(low_pc, high_pc, leaf->ranges[i].low_pc, leaf->ranges[i].high_pc))
        {
            if (low_pc < leaf->ranges[i].low_pc)
                leaf->ranges[i].low_pc = low_pc;
            if (high_pc > leaf->ranges[i].high_pc)
                leaf->ranges[i].high_pc = high_pc;
            return true;
        }
    }
    return false;
}

static bool check_splitting_will_help(struct trie_leaf *leaf, bfd_vma trie_pc,
                                      unsigned int trie_pc_bits)
{
    bfd_vma bucket_high_pc = trie_pc + ((bfd_vma)-1 >> trie_pc_bits);
    for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
    {
        if (leaf->ranges[i].low_pc > trie_pc || leaf->ranges[i].high_pc <= bucket_high_pc)
            return true;
    }
    return false;
}

static struct trie_node *convert_leaf_to_interior(bfd *abfd, struct trie_leaf *leaf,
                                                  bfd_vma trie_pc, unsigned int trie_pc_bits)
{
    struct trie_interior *interior = bfd_zalloc(abfd, sizeof(struct trie_interior));
    if (!interior)
        return NULL;

    for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
    {
        if (!insert_arange_in_trie(abfd, &interior->head, trie_pc, trie_pc_bits,
                                   leaf->ranges[i].unit, leaf->ranges[i].low_pc,
                                   leaf->ranges[i].high_pc))
            return NULL;
    }
    return &interior->head;
}

static struct trie_node *expand_leaf(bfd *abfd, struct trie_leaf *leaf)
{
    unsigned int new_room_in_leaf = leaf->head.num_room_in_leaf * 2;
    size_t amt = sizeof(*leaf) + new_room_in_leaf * sizeof(leaf->ranges[0]);
    struct trie_leaf *new_leaf = bfd_zalloc(abfd, amt);
    
    new_leaf->head.num_room_in_leaf = new_room_in_leaf;
    new_leaf->num_stored_in_leaf = leaf->num_stored_in_leaf;
    memcpy(new_leaf->ranges, leaf->ranges,
           leaf->num_stored_in_leaf * sizeof(leaf->ranges[0]));
    
    return &new_leaf->head;
}

static void add_range_to_leaf(struct trie_leaf *leaf, struct comp_unit *unit,
                              bfd_vma low_pc, bfd_vma high_pc)
{
    unsigned int i = leaf->num_stored_in_leaf++;
    leaf->ranges[i].unit = unit;
    leaf->ranges[i].low_pc = low_pc;
    leaf->ranges[i].high_pc = high_pc;
}

static void clamp_range_to_bucket(bfd_vma *clamped_low_pc, bfd_vma *clamped_high_pc,
                                  bfd_vma low_pc, bfd_vma high_pc,
                                  bfd_vma trie_pc, unsigned int trie_pc_bits)
{
    *clamped_low_pc = low_pc;
    *clamped_high_pc = high_pc;
    
    if (trie_pc_bits > 0)
    {
        bfd_vma bucket_high_pc = trie_pc + ((bfd_vma)-1 >> trie_pc_bits);
        if (*clamped_low_pc < trie_pc)
            *clamped_low_pc = trie_pc;
        if (*clamped_high_pc > bucket_high_pc)
            *clamped_high_pc = bucket_high_pc;
    }
}

#define BITS_PER_BYTE 8
#define BYTE_MASK 0xff

static struct trie_node *insert_into_interior(bfd *abfd, struct trie_interior *interior,
                                              bfd_vma trie_pc, unsigned int trie_pc_bits,
                                              struct comp_unit *unit,
                                              bfd_vma clamped_low_pc, bfd_vma clamped_high_pc,
                                              bfd_vma low_pc, bfd_vma high_pc)
{
    int from_ch = (clamped_low_pc >> (VMA_BITS - trie_pc_bits - BITS_PER_BYTE)) & BYTE_MASK;
    int to_ch = ((clamped_high_pc - 1) >> (VMA_BITS - trie_pc_bits - BITS_PER_BYTE)) & BYTE_MASK;
    
    for (int ch = from_ch; ch <= to_ch; ++ch)
    {
        struct trie_node *child = interior->children[ch];
        if (child == NULL)
        {
            child = alloc_trie_leaf(abfd);
            if (!child)
                return NULL;
        }
        
        bfd_vma bucket = (bfd_vma)ch << (VMA_BITS - trie_pc_bits - BITS_PER_BYTE);
        child = insert_arange_in_trie(abfd, child, trie_pc + bucket,
                                      trie_pc_bits + BITS_PER_BYTE,
                                      unit, low_pc, high_pc);
        if (!child)
            return NULL;
        
        interior->children[ch] = child;
    }
    return &interior->head;
}

static struct trie_node *insert_arange_in_trie(bfd *abfd, struct trie_node *trie,
                                               bfd_vma trie_pc, unsigned int trie_pc_bits,
                                               struct comp_unit *unit,
                                               bfd_vma low_pc, bfd_vma high_pc)
{
    bool is_full_leaf = false;
    bool splitting_leaf_will_help = false;

    if (trie->num_room_in_leaf > 0)
    {
        struct trie_leaf *leaf = (struct trie_leaf *)trie;
        
        if (try_extend_existing_range(leaf, unit, low_pc, high_pc))
            return trie;

        is_full_leaf = leaf->num_stored_in_leaf == trie->num_room_in_leaf;
        
        if (is_full_leaf && trie_pc_bits < VMA_BITS)
            splitting_leaf_will_help = check_splitting_will_help(leaf, trie_pc, trie_pc_bits);
    }

    if (is_full_leaf && splitting_leaf_will_help)
    {
        trie = convert_leaf_to_interior(abfd, (struct trie_leaf *)trie, trie_pc, trie_pc_bits);
        if (!trie)
            return NULL;
        is_full_leaf = false;
    }

    if (is_full_leaf)
    {
        trie = expand_leaf(abfd, (struct trie_leaf *)trie);
        is_full_leaf = false;
    }

    if (trie->num_room_in_leaf > 0)
    {
        struct trie_leaf *leaf = (struct trie_leaf *)trie;
        add_range_to_leaf(leaf, unit, low_pc, high_pc);
        return trie;
    }

    bfd_vma clamped_low_pc, clamped_high_pc;
    clamp_range_to_bucket(&clamped_low_pc, &clamped_high_pc, low_pc, high_pc, trie_pc, trie_pc_bits);
    
    return insert_into_interior(abfd, (struct trie_interior *)trie, trie_pc, trie_pc_bits,
                                unit, clamped_low_pc, clamped_high_pc, low_pc, high_pc);
}

static bool is_empty_range(bfd_vma low_pc, bfd_vma high_pc)
{
    return low_pc == high_pc;
}

static bool insert_into_trie(struct comp_unit *unit, struct trie_node **trie_root,
                             bfd_vma low_pc, bfd_vma high_pc)
{
    *trie_root = insert_arange_in_trie(unit->file->bfd_ptr,
                                       *trie_root,
                                       0,
                                       0,
                                       unit,
                                       low_pc,
                                       high_pc);
    return *trie_root != NULL;
}

static bool use_empty_first_arange(struct arange *first_arange,
                                   bfd_vma low_pc, bfd_vma high_pc)
{
    if (first_arange->high == 0)
    {
        first_arange->low = low_pc;
        first_arange->high = high_pc;
        return true;
    }
    return false;
}

static bool extend_existing_range(struct arange *first_arange,
                                  bfd_vma low_pc, bfd_vma high_pc)
{
    struct arange *arange = first_arange;
    
    while (arange)
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
    return false;
}

static bool allocate_new_arange(struct comp_unit *unit, struct arange *first_arange,
                                bfd_vma low_pc, bfd_vma high_pc)
{
    struct arange *arange = (struct arange *) bfd_alloc(unit->abfd, sizeof(*arange));
    if (arange == NULL)
        return false;
    
    arange->low = low_pc;
    arange->high = high_pc;
    arange->next = first_arange->next;
    first_arange->next = arange;
    return true;
}

static bool
arange_add(struct comp_unit *unit, struct arange *first_arange,
          struct trie_node **trie_root, bfd_vma low_pc, bfd_vma high_pc)
{
    if (is_empty_range(low_pc, high_pc))
        return true;

    if (trie_root != NULL)
    {
        if (!insert_into_trie(unit, trie_root, low_pc, high_pc))
            return false;
    }

    if (use_empty_first_arange(first_arange, low_pc, high_pc))
        return true;

    if (extend_existing_range(first_arange, low_pc, high_pc))
        return true;

    return allocate_new_arange(unit, first_arange, low_pc, high_pc);
}

/* Compare function for line sequences.  */

static int
compare_values(long long val1, long long val2, int ascending)
{
  if (val1 < val2)
    return ascending ? -1 : 1;
  if (val1 > val2)
    return ascending ? 1 : -1;
  return 0;
}

static int
compare_sequences (const void* a, const void* b)
{
  const struct line_sequence* seq1 = a;
  const struct line_sequence* seq2 = b;
  int result;

  result = compare_values(seq1->low_pc, seq2->low_pc, 1);
  if (result != 0)
    return result;

  result = compare_values(seq1->last_line->address, seq2->last_line->address, 0);
  if (result != 0)
    return result;

  result = compare_values(seq1->last_line->op_index, seq2->last_line->op_index, 0);
  if (result != 0)
    return result;

  return compare_values(seq1->num_lines, seq2->num_lines, 1);
}

/* Construct the line information table for quick lookup.  */

static bool
build_line_info_table (struct line_info_table *  table,
		       struct line_sequence *    seq)
{
  if (seq->line_info_lookup != NULL)
    return true;

  unsigned int num_lines = count_lines(seq);
  seq->num_lines = num_lines;
  
  if (num_lines == 0)
    return true;

  struct line_info **line_info_lookup = allocate_lookup_table(table, num_lines);
  seq->line_info_lookup = line_info_lookup;
  
  if (line_info_lookup == NULL)
    return false;

  populate_lookup_table(seq, line_info_lookup, num_lines);
  return true;
}

static unsigned int
count_lines(struct line_sequence *seq)
{
  unsigned int num_lines = 0;
  struct line_info *each_line = seq->last_line;
  
  while (each_line != NULL) {
    num_lines++;
    each_line = each_line->prev_line;
  }
  
  return num_lines;
}

static struct line_info **
allocate_lookup_table(struct line_info_table *table, unsigned int num_lines)
{
  size_t amt = sizeof(struct line_info*) * num_lines;
  return (struct line_info**) bfd_alloc(table->abfd, amt);
}

static void
populate_lookup_table(struct line_sequence *seq, struct line_info **line_info_lookup, unsigned int num_lines)
{
  unsigned int line_index = num_lines;
  struct line_info *each_line = seq->last_line;
  
  while (each_line != NULL) {
    line_info_lookup[--line_index] = each_line;
    each_line = each_line->prev_line;
  }
  
  BFD_ASSERT(line_index == 0);
}

/* Sort the line sequences for quick lookup.  */

static bool allocate_sequences(struct line_info_table* table, struct line_sequence **sequences)
{
  size_t amt = sizeof(struct line_sequence) * table->num_sequences;
  *sequences = (struct line_sequence *) bfd_alloc(table->abfd, amt);
  return *sequences != NULL;
}

static void copy_sequence_data(struct line_sequence *dest, struct line_sequence *src, unsigned int index)
{
  dest->low_pc = src->low_pc;
  dest->prev_sequence = NULL;
  dest->last_line = src->last_line;
  dest->line_info_lookup = NULL;
  dest->num_lines = index;
}

static void copy_sequences_to_array(struct line_info_table* table, struct line_sequence *sequences)
{
  struct line_sequence *seq = table->sequences;
  
  for (unsigned int n = 0; n < table->num_sequences; n++)
  {
    struct line_sequence* last_seq = seq;
    BFD_ASSERT(seq);
    copy_sequence_data(&sequences[n], seq, n);
    seq = seq->prev_sequence;
    free(last_seq);
  }
  BFD_ASSERT(seq == NULL);
}

static bool is_nested_sequence(struct line_sequence *seq, bfd_vma last_high_pc)
{
  return seq->last_line->address <= last_high_pc;
}

static bool is_overlapping_sequence(struct line_sequence *seq, bfd_vma last_high_pc)
{
  return seq->low_pc < last_high_pc;
}

static void compact_sequence(struct line_sequence *dest, struct line_sequence *src)
{
  dest->low_pc = src->low_pc;
  dest->last_line = src->last_line;
}

static unsigned int trim_and_compact_sequences(struct line_sequence *sequences, unsigned int total_sequences)
{
  unsigned int num_sequences = 1;
  bfd_vma last_high_pc = sequences[0].last_line->address;
  
  for (unsigned int n = 1; n < total_sequences; n++)
  {
    if (is_overlapping_sequence(&sequences[n], last_high_pc))
    {
      if (is_nested_sequence(&sequences[n], last_high_pc))
        continue;
      sequences[n].low_pc = last_high_pc;
    }
    
    last_high_pc = sequences[n].last_line->address;
    
    if (n > num_sequences)
      compact_sequence(&sequences[num_sequences], &sequences[n]);
    
    num_sequences++;
  }
  
  return num_sequences;
}

static bool sort_line_sequences(struct line_info_table* table)
{
  struct line_sequence *sequences;
  
  if (table->num_sequences == 0)
    return true;
  
  if (!allocate_sequences(table, &sequences))
    return false;
  
  copy_sequences_to_array(table, sequences);
  
  qsort(sequences, table->num_sequences, sizeof(struct line_sequence), compare_sequences);
  
  table->num_sequences = trim_and_compact_sequences(sequences, table->num_sequences);
  table->sequences = sequences;
  
  return true;
}

/* Add directory to TABLE.  CUR_DIR memory ownership is taken by TABLE.  */

static bool needs_reallocation(size_t num_dirs)
{
  return (num_dirs % DIR_ALLOC_CHUNK) == 0;
}

static bool reallocate_dirs(struct line_info_table *table)
{
  size_t new_capacity = table->num_dirs + DIR_ALLOC_CHUNK;
  size_t amt = new_capacity * sizeof(char *);
  
  char **tmp = (char **) bfd_realloc(table->dirs, amt);
  if (tmp == NULL)
    return false;
    
  table->dirs = tmp;
  return true;
}

static bool
line_info_add_include_dir (struct line_info_table *table, char *cur_dir)
{
  if (needs_reallocation(table->num_dirs))
    {
      if (!reallocate_dirs(table))
        return false;
    }

  table->dirs[table->num_dirs++] = cur_dir;
  return true;
}

static bool
line_info_add_include_dir_stub (struct line_info_table *table, char *cur_dir,
				unsigned int dir ATTRIBUTE_UNUSED,
				unsigned int xtime ATTRIBUTE_UNUSED,
				unsigned int size ATTRIBUTE_UNUSED)
{
  return line_info_add_include_dir (table, cur_dir);
}

/* Add file to TABLE.  CUR_FILE memory ownership is taken by TABLE.  */

static bool
reallocate_files_if_needed(struct line_info_table *table)
{
  if ((table->num_files % FILE_ALLOC_CHUNK) != 0)
    return true;

  size_t amt = (table->num_files + FILE_ALLOC_CHUNK) * sizeof(struct fileinfo);
  struct fileinfo *tmp = (struct fileinfo *) bfd_realloc(table->files, amt);
  
  if (tmp == NULL)
    return false;
    
  table->files = tmp;
  return true;
}

static void
set_file_info(struct fileinfo *file, char *name, unsigned int dir,
              unsigned int xtime, unsigned int size)
{
  file->name = name;
  file->dir = dir;
  file->time = xtime;
  file->size = size;
}

static bool
line_info_add_file_name(struct line_info_table *table, char *cur_file,
                       unsigned int dir, unsigned int xtime,
                       unsigned int size)
{
  if (!reallocate_files_if_needed(table))
    return false;

  set_file_info(&table->files[table->num_files], cur_file, dir, xtime, size);
  table->num_files++;
  
  return true;
}

/* Read directory or file name entry format, starting with byte of
   format count entries, ULEB128 pairs of entry formats, ULEB128 of
   entries count and the entries themselves in the described entry
   format.  */

static bool
validate_format_and_data_count(bfd_byte format_count, bfd_vma data_count, bfd_byte *buf, bfd_byte *buf_end)
{
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

  return true;
}

static void
skip_format_header(bfd *abfd, bfd_byte **buf, bfd_byte *buf_end, bfd_byte format_count)
{
  bfd_byte formati;
  for (formati = 0; formati < format_count; formati++)
    {
      _bfd_safe_read_leb128 (abfd, buf, false, buf_end);
      _bfd_safe_read_leb128 (abfd, buf, false, buf_end);
    }
}

static bool
get_content_destination(bfd_vma content_type, struct fileinfo *fe, 
                        char ***stringp, unsigned int **uintp)
{
  char *string_trash;
  unsigned int uint_trash;
  
  *stringp = &string_trash;
  *uintp = &uint_trash;

  switch (content_type)
    {
    case DW_LNCT_path:
      *stringp = &fe->name;
      break;
    case DW_LNCT_directory_index:
      *uintp = &fe->dir;
      break;
    case DW_LNCT_timestamp:
      *uintp = &fe->time;
      break;
    case DW_LNCT_size:
      *uintp = &fe->size;
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
  return true;
}

static void
assign_attribute_value(bfd_vma form, struct attribute *attr, char **stringp, unsigned int *uintp)
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

static bool
process_format_entry(bfd *abfd, bfd_byte **format, bfd_byte **buf, bfd_byte *buf_end,
                    struct comp_unit *unit, struct fileinfo *fe)
{
  bfd_vma content_type, form;
  char **stringp;
  unsigned int *uintp;
  struct attribute attr;

  content_type = _bfd_safe_read_leb128 (abfd, format, false, buf_end);
  
  if (!get_content_destination(content_type, fe, &stringp, &uintp))
    return false;

  form = _bfd_safe_read_leb128 (abfd, format, false, buf_end);
  *buf = read_attribute_value (&attr, form, 0, unit, *buf, buf_end);
  
  if (*buf == NULL)
    return false;
    
  assign_attribute_value(form, &attr, stringp, uintp);
  return true;
}

static bool
process_single_entry(bfd *abfd, bfd_byte **buf, bfd_byte *buf_end,
                    bfd_byte *format_header_data, bfd_byte format_count,
                    struct comp_unit *unit, struct line_info_table *table,
                    bool (*callback) (struct line_info_table *table,
                                     char *cur_file,
                                     unsigned int dir,
                                     unsigned int time,
                                     unsigned int size))
{
  bfd_byte *format = format_header_data;
  struct fileinfo fe;
  bfd_byte formati;

  memset (&fe, 0, sizeof fe);
  
  for (formati = 0; formati < format_count; formati++)
    {
      if (!process_format_entry(abfd, &format, buf, buf_end, unit, &fe))
        return false;
    }

  return callback (table, fe.name, fe.dir, fe.time, fe.size);
}

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
  bfd_byte format_count;
  bfd_vma data_count, datai;
  bfd_byte *buf = *bufp;
  bfd_byte *format_header_data;

  format_count = read_1_byte (abfd, &buf, buf_end);
  format_header_data = buf;
  
  skip_format_header(abfd, &buf, buf_end, format_count);

  data_count = _bfd_safe_read_leb128 (abfd, &buf, false, buf_end);
  
  if (!validate_format_and_data_count(format_count, data_count, buf, buf_end))
    return false;

  for (datai = 0; datai < data_count; datai++)
    {
      if (!process_single_entry(abfd, &buf, buf_end, format_header_data, 
                               format_count, unit, table, callback))
        return false;
    }

  *bufp = buf;
  return true;
}

/* Decode the line number information for UNIT.  */

static bool validate_line_info_size(struct dwarf2_debug_file *file)
{
  if (file->dwarf_line_size < 16)
    {
      _bfd_error_handler
        (_("DWARF error: line info section is too small (%" PRId64 ")"),
         (int64_t) file->dwarf_line_size);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool read_total_length(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
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

static bool validate_version(struct line_head *lh)
{
  if (lh->version < 2 || lh->version > 5)
    {
      _bfd_error_handler
        (_("DWARF error: unhandled .debug_line version %d"), lh->version);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool check_prologue_space(bfd_byte *line_ptr, bfd_byte *line_end,
                                 struct line_head *lh, unsigned int offset_size)
{
  unsigned int min_size = offset_size + (lh->version >= 5 ? 8 : (lh->version >= 4 ? 6 : 5));
  if (line_ptr + min_size >= line_end)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading prologue"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool read_version5_header(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end)
{
  unsigned int segment_selector_size;
  
  read_1_byte (abfd, line_ptr, line_end);
  segment_selector_size = read_1_byte (abfd, line_ptr, line_end);
  
  if (segment_selector_size != 0)
    {
      _bfd_error_handler
        (_("DWARF error: line info unsupported segment selector size %u"),
         segment_selector_size);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static void read_prologue_length(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                 struct line_head *lh, unsigned int offset_size)
{
  if (offset_size == 4)
    lh->prologue_length = read_4_bytes (abfd, line_ptr, line_end);
  else
    lh->prologue_length = read_8_bytes (abfd, line_ptr, line_end);
}

static bool read_instruction_info(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                  struct line_head *lh)
{
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
  
  return true;
}

static bool read_opcode_lengths(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                struct line_head *lh)
{
  unsigned int i;
  size_t amt;
  
  if (*line_ptr + (lh->opcode_base - 1) >= line_end)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading opcodes"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  
  amt = lh->opcode_base * sizeof (unsigned char);
  lh->standard_opcode_lengths = (unsigned char *) bfd_alloc (abfd, amt);
  lh->standard_opcode_lengths[0] = 1;
  
  for (i = 1; i < lh->opcode_base; ++i)
    lh->standard_opcode_lengths[i] = read_1_byte (abfd, line_ptr, line_end);
  
  return true;
}

static struct line_info_table* allocate_line_table(bfd *abfd, struct comp_unit *unit)
{
  size_t amt = sizeof (struct line_info_table);
  struct line_info_table* table = (struct line_info_table *) bfd_alloc (abfd, amt);
  
  if (table == NULL)
    return NULL;
    
  table->abfd = abfd;
  table->comp_dir = unit->comp_dir;
  table->num_files = 0;
  table->files = NULL;
  table->num_dirs = 0;
  table->dirs = NULL;
  table->num_sequences = 0;
  table->sequences = NULL;
  table->lcl_head = NULL;
  
  return table;
}

static bool read_file_and_dir_tables(struct comp_unit *unit, bfd_byte **line_ptr,
                                     bfd_byte *line_end, struct line_info_table *table,
                                     struct line_head *lh, bfd *abfd)
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
          unsigned int dir = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
          unsigned int xtime = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
          unsigned int size = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
          
          if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
            return false;
        }
      table->use_dir_and_file_0 = false;
    }
  return true;
}

static void update_address_bounds(bfd_vma address, bfd_vma *low_pc, bfd_vma *high_pc)
{
  if (address < *low_pc)
    *low_pc = address;
  if (address > *high_pc)
    *high_pc = address;
}

static void calculate_special_opcode_address(struct line_head *lh, unsigned char adj_opcode,
                                             bfd_vma *address, unsigned char *op_index)
{
  if (lh->maximum_ops_per_insn == 1)
    {
      *address += (adj_opcode / lh->line_range * lh->minimum_instruction_length);
    }
  else
    {
      *address += ((*op_index + adj_opcode / lh->line_range)
                   / lh->maximum_ops_per_insn * lh->minimum_instruction_length);
      *op_index = ((*op_index + adj_opcode / lh->line_range)
                   % lh->maximum_ops_per_insn);
    }
}

static bool process_extended_opcode(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                    unsigned char extended_op, unsigned int exop_len,
                                    struct line_info_table *table, struct comp_unit *unit,
                                    bfd_vma *address, unsigned char *op_index,
                                    char *filename, unsigned int line, unsigned int column,
                                    unsigned int *discriminator, int *end_sequence,
                                    bfd_vma *low_pc, bfd_vma *high_pc)
{
  switch (extended_op)
    {
    case DW_LNE_end_sequence:
      *end_sequence = 1;
      if (!add_line_info (table, *address, *op_index, filename, line,
                          column, *discriminator, *end_sequence))
        return false;
      *discriminator = 0;
      update_address_bounds(*address, low_pc, high_pc);
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
                       *low_pc, *high_pc))
        return false;
      break;
    case DW_LNE_set_address:
      *address = read_address (unit, line_ptr, line_end);
      *op_index = 0;
      break;
    case DW_LNE_define_file:
      {
        char *cur_file = read_string (line_ptr, line_end);
        unsigned int dir = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
        unsigned int xtime = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
        unsigned int size = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
        if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
          return false;
      }
      break;
    case DW_LNE_set_discriminator:
      *discriminator = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
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

static void advance_pc(struct line_head *lh, bfd *abfd, bfd_byte **line_ptr,
                       bfd_byte *line_end, bfd_vma *address, unsigned char *op_index)
{
  if (lh->maximum_ops_per_insn == 1)
    {
      *address += (lh->minimum_instruction_length
                   * _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end));
    }
  else
    {
      bfd_vma adjust = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
      *address = ((*op_index + adjust) / lh->maximum_ops_per_insn
                  * lh->minimum_instruction_length);
      *op_index = (*op_index + adjust) % lh->maximum_ops_per_insn;
    }
}

static void const_add_pc(struct line_head *lh, bfd_vma *address, unsigned char *op_index)
{
  #define CONST_ADD_PC_ADJUST_BASE 255
  
  if (lh->maximum_ops_per_insn == 1)
    {
      *address += (lh->minimum_instruction_length
                   * ((CONST_ADD_PC_ADJUST_BASE - lh->opcode_base) / lh->line_range));
    }
  else
    {
      bfd_vma adjust = ((CONST_ADD_PC_ADJUST_BASE - lh->opcode_base) / lh->line_range);
      *address += (lh->minimum_instruction_length
                   * ((*op_index + adjust) / lh->maximum_ops_per_insn));
      *op_index = (*op_index + adjust) % lh->maximum_ops_per_insn;
    }
}

static bool process_standard_opcode(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                    unsigned char op_code, struct line_head *lh,
                                    struct line_info_table *table,
                                    bfd_vma *address, unsigned char *op_index,
                                    char **filename, unsigned int *line, unsigned int *column,
                                    unsigned int *discriminator, int *is_stmt,
                                    bfd_vma *low_pc, bfd_vma *high_pc)
{
  unsigned int i;
  
  switch (op_code)
    {
    case DW_LNS_extended_op:
      {
        unsigned int exop_len = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
        unsigned char extended_op = read_1_byte (abfd, line_ptr, line_end);
        int end_sequence = 0;
        if (!process_extended_opcode(abfd, line_ptr, line_end, extended_op, exop_len,
                                     table, table->comp_dir->unit, address, op_index,
                                     *filename, *line, *column, discriminator,
                                     &end_sequence, low_pc, high_pc))
          return false;
      }
      break;
    case DW_LNS_copy:
      if (!add_line_info (table, *address, *op_index, *filename, *line,
                          *column, *discriminator, 0))
        return false;
      *discriminator = 0;
      update_address_bounds(*address, low_pc, high_pc);
      break;
    case DW_LNS_advance_pc:
      advance_pc(lh, abfd, line_ptr, line_end, address, op_index);
      break;
    case DW_LNS_advance_line:
      *line += _bfd_safe_read_leb128 (abfd, line_ptr, true, line_end);
      break;
    case DW_LNS_set_file:
      {
        unsigned int filenum = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
        free (*filename);
        *filename = concat_filename (table, filenum);
      }
      break;
    case DW_LNS_set_column:
      *column = _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
      break;
    case DW_LNS_negate_stmt:
      *is_stmt = !(*is_stmt);
      break;
    case DW_LNS_set_basic_block:
      break;
    case DW_LNS_const_add_pc:
      if (lh->line_range == 0)
        return false;
      const_add_pc(lh, address, op_index);
      break;
    case DW_LNS_fixed_advance_pc:
      *address += read_2_bytes (abfd, line_ptr, line_end);
      *op_index = 0;
      break;
    default:
      for (i = 0; i < lh->standard_opcode_lengths[op_code]; i++)
        (void) _bfd_safe_read_leb128 (abfd, line_ptr, false, line_end);
      break;
    }
  return true;
}

static bool decode_line_sequence(bfd *abfd, bfd_byte **line_ptr, bfd_byte *line_end,
                                 struct line_head *lh, struct line_info_table *table,
                                 struct comp_unit *unit)
{
  bfd_vma address = 0;
  unsigned char op_index = 0;
  char *filename = NULL;
  unsigned int line = 1;
  unsigned int column = 0;
  unsigned int discriminator = 0;
  int is_stmt = lh->default_is_stmt;
  int end_sequence = 0;
  bfd_vma low_pc = (bfd_vma) -1;
  bfd_vma high_pc = 0;
  
  if (table->num_files)
    filename = concat_filename (table, 1);
  
  while (!end_sequence && *line_ptr < line_end)
    {
      unsigned char op_code = read_1_byte (abfd, line_ptr, line_end);
      
      if (op_code >= lh->opcode_base)
        {
          unsigned char adj_opcode = op_code - lh->opcode_base;
          if (lh->line_range == 0)
            {
              free (filename);
              return false;
            }
          calculate_special_opcode_address(lh, adj_opcode, &address, &op_index);
          line += lh->line_base + (adj_opcode % lh->line_range);
          
          if (!add_line_info (table, address, op_index, filename,
                              line, column, discriminator, 0))
            {
              free (filename);
              return false;
            }
          discriminator = 0;
          update_address_bounds(address, &low_pc, &high_pc);
        }
      else
        {
          if (!process_standard_opcode(abfd, line_ptr, line_end, op_code, lh,
                                       table, &address, &op_index, &filename,
                                       &line, &column, &discriminator, &is_stmt,
                                       &low_pc, &high_pc))
            {
              free (filename);
              return false;
            }
        }
    }
  
  free (filename);
  return true;
}

static void cleanup_table(struct line_info_table *table)
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
  unsigned int offset_size;

  if (unit->line_offset == 0 && file->line_table)
    return file->line_table;

  if (!read_section (abfd, &stash->debug_sections[debug_line],
                     file->syms, unit->line_offset,
                     &file->dwarf_line_buffer, &file->dwarf_line_size))
    return NULL;

  if (!validate_line_info_size(file))
    return NULL;
    
  line_ptr = file->dwarf_line_buffer + unit->line_offset;
  line_end = file->dwarf_line_buffer + file->dwarf_line_size;

  if (!read_total_length(abfd, &line_ptr, line_end, &lh, &offset_size, unit))
    return NULL;

  line_end = line_ptr + lh.total_length;

  lh.version = read_2_bytes (abfd, &line_ptr, line_end);
  if (!validate_version(&lh))
    return NULL;

  if (!check_prologue_space(line_ptr, line_end, &lh, offset_size))
    return NULL;

  if (lh.version >= 5)
    {
      if (!read_version5_header(abfd, &line_ptr, line_end))
        return NULL;
    }

  read_prologue_length(abfd, &line_ptr, line_end, &lh, offset_size);
  
  if (!read_instruction_info(abfd, &line_ptr, line_end, &lh))
    return NULL;

  if (!read_opcode_lengths(abfd, &line_ptr, line_end, &lh))
    return NULL;

  table = allocate_line_table(abfd, unit);
  if (table == NULL)
    return NULL;

  if (!read_file_and_dir_tables(unit, &line_ptr, line_end, table, &lh, abfd))
    goto fail;

  while (line_ptr < line_end)
    {
      if (!decode_line_sequence(abfd, &line_ptr, line_end, &lh, table, unit))
        goto fail;
    }

  if (unit->line_offset == 0)
    file->line_table = table;
  if (sort_line_sequences (table))
    return table;

 fail:
  cleanup_table(table);
  return NULL;
}

/* If ADDR is within TABLE set the output parameters and return TRUE,
   otherwise set *FILENAME_PTR to NULL and return FALSE.
   The parameters FILENAME_PTR, LINENUMBER_PTR and DISCRIMINATOR_PTR
   are pointers to the objects to be filled in.  */

static bool
is_address_in_sequence_range(struct line_sequence *seq, bfd_vma addr)
{
  return seq && addr >= seq->low_pc && addr < seq->last_line->address;
}

static struct line_sequence *
binary_search_sequence(struct line_info_table *table, bfd_vma addr)
{
  int low = 0;
  int high = table->num_sequences;
  
  while (low < high)
    {
      int mid = (low + high) / 2;
      struct line_sequence *seq = &table->sequences[mid];
      
      if (addr < seq->low_pc)
        high = mid;
      else if (addr >= seq->last_line->address)
        low = mid + 1;
      else
        return seq;
    }
  
  return NULL;
}

static struct line_info *
binary_search_line_info(struct line_sequence *seq, bfd_vma addr)
{
  int low = 0;
  int high = seq->num_lines;
  int mid = 0;
  
  while (low < high)
    {
      mid = (low + high) / 2;
      struct line_info *info = seq->line_info_lookup[mid];
      
      if (addr < info->address)
        high = mid;
      else if (addr >= seq->line_info_lookup[mid + 1]->address)
        low = mid + 1;
      else
        return info;
    }
  
  return (mid < seq->num_lines) ? seq->line_info_lookup[mid] : NULL;
}

static bool
is_valid_line_info(struct line_info *info, struct line_sequence *seq, 
                   bfd_vma addr, int index)
{
  if (!info)
    return false;
    
  if (addr < info->address)
    return false;
    
  if (addr >= seq->line_info_lookup[index + 1]->address)
    return false;
    
  if (info->end_sequence || info == seq->last_line)
    return false;
    
  return true;
}

static void
set_line_info_results(const struct line_info *info,
                     const char **filename_ptr,
                     unsigned int *linenumber_ptr,
                     unsigned int *discriminator_ptr)
{
  *filename_ptr = info->filename;
  *linenumber_ptr = info->line;
  if (discriminator_ptr)
    *discriminator_ptr = info->discriminator;
}

static void
clear_results(const char **filename_ptr)
{
  *filename_ptr = NULL;
}

static bool
lookup_address_in_line_info_table (struct line_info_table *table,
                                  bfd_vma addr,
                                  const char **filename_ptr,
                                  unsigned int *linenumber_ptr,
                                  unsigned int *discriminator_ptr)
{
  struct line_sequence *seq = binary_search_sequence(table, addr);
  
  if (!is_address_in_sequence_range(seq, addr))
    {
      clear_results(filename_ptr);
      return false;
    }
    
  if (!build_line_info_table(table, seq))
    {
      clear_results(filename_ptr);
      return false;
    }
    
  struct line_info *info = binary_search_line_info(seq, addr);
  int info_index = info ? (info - seq->line_info_lookup[0]) : 0;
  
  if (is_valid_line_info(info, seq, addr, info_index))
    {
      set_line_info_results(info, filename_ptr, linenumber_ptr, 
                           discriminator_ptr);
      return true;
    }
    
  clear_results(filename_ptr);
  return false;
}

/* Read in the .debug_ranges section for future reference.  */

static bool
read_debug_ranges (struct comp_unit * unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  return read_section (unit->abfd, &stash->debug_sections[debug_ranges],
		       file->syms, 0,
		       &file->dwarf_ranges_buffer, &file->dwarf_ranges_size);
}

/* Read in the .debug_rnglists section for future reference.  */

static bool
read_debug_rnglists (struct comp_unit * unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  return read_section (unit->abfd, &stash->debug_sections[debug_rnglists],
		       file->syms, 0,
		       &file->dwarf_rnglists_buffer, &file->dwarf_rnglists_size);
}

/* Function table functions.  */

static int
compare_values(long long val1, long long val2)
{
  if (val1 < val2)
    return -1;
  if (val1 > val2)
    return 1;
  return 0;
}

static int
compare_lookup_funcinfos(const void *a, const void *b)
{
  const struct lookup_funcinfo *lookup1 = a;
  const struct lookup_funcinfo *lookup2 = b;
  int result;

  result = compare_values(lookup1->low_addr, lookup2->low_addr);
  if (result != 0)
    return result;

  result = compare_values(lookup1->high_addr, lookup2->high_addr);
  if (result != 0)
    return result;

  return compare_values(lookup1->idx, lookup2->idx);
}

static bool
should_skip_table_creation(struct comp_unit *unit)
{
    return unit->lookup_funcinfo_table || unit->number_of_functions == 0;
}

static struct lookup_funcinfo *
allocate_lookup_table(unsigned int number_of_functions)
{
    return (struct lookup_funcinfo *)
        bfd_malloc(number_of_functions * sizeof(struct lookup_funcinfo));
}

static void
calculate_address_range(struct lookup_funcinfo *entry)
{
    bfd_vma low_addr = entry->funcinfo->arange.low;
    bfd_vma high_addr = entry->funcinfo->arange.high;
    struct arange *range;

    for (range = entry->funcinfo->arange.next; range; range = range->next)
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
populate_lookup_entry(struct lookup_funcinfo *entry, struct funcinfo *funcinfo, size_t idx)
{
    entry->funcinfo = funcinfo;
    entry->idx = idx;
    calculate_address_range(entry);
}

static size_t
populate_lookup_table(struct lookup_funcinfo *lookup_funcinfo_table, struct comp_unit *unit)
{
    size_t func_index = unit->number_of_functions;
    struct funcinfo *each;

    for (each = unit->function_table; each; each = each->prev_func)
    {
        populate_lookup_entry(&lookup_funcinfo_table[--func_index], each, func_index);
    }

    return func_index;
}

static void
update_high_watermarks(struct lookup_funcinfo *lookup_funcinfo_table, unsigned int number_of_functions)
{
    bfd_vma high_addr = lookup_funcinfo_table[0].high_addr;
    size_t func_index;

    for (func_index = 1; func_index < number_of_functions; func_index++)
    {
        struct lookup_funcinfo *entry = &lookup_funcinfo_table[func_index];
        if (entry->high_addr > high_addr)
            high_addr = entry->high_addr;
        else
            entry->high_addr = high_addr;
    }
}

static bool
build_lookup_funcinfo_table(struct comp_unit *unit)
{
    struct lookup_funcinfo *lookup_funcinfo_table;
    size_t func_index;

    if (should_skip_table_creation(unit))
        return true;

    lookup_funcinfo_table = allocate_lookup_table(unit->number_of_functions);
    if (lookup_funcinfo_table == NULL)
        return false;

    func_index = populate_lookup_table(lookup_funcinfo_table, unit);
    BFD_ASSERT(func_index == 0);

    qsort(lookup_funcinfo_table,
          unit->number_of_functions,
          sizeof(struct lookup_funcinfo),
          compare_lookup_funcinfos);

    update_high_watermarks(lookup_funcinfo_table, unit->number_of_functions);

    unit->lookup_funcinfo_table = lookup_funcinfo_table;
    return true;
}

/* If ADDR is within UNIT's function tables, set FUNCTION_PTR, and return
   TRUE.  Note that we need to find the function that has the smallest range
   that contains ADDR, to handle inlined functions without depending upon
   them being ordered in TABLE by increasing range.  */

static bool
is_address_in_range(bfd_vma addr, bfd_vma low, bfd_vma high)
{
  return addr >= low && addr < high;
}

static bfd_vma
get_range_length(struct arange *arange)
{
  return arange->high - arange->low;
}

static bool
is_better_fit(struct arange *arange, bfd_vma best_fit_len, struct funcinfo *funcinfo, struct funcinfo *best_fit)
{
  bfd_vma range_len = get_range_length(arange);
  return range_len < best_fit_len || 
         (range_len == best_fit_len && funcinfo > best_fit);
}

static bfd_size_type
binary_search_first_function(struct comp_unit *unit, bfd_vma addr, unsigned int number_of_functions)
{
  bfd_size_type low = 0;
  bfd_size_type high = number_of_functions;
  bfd_size_type first = high;
  
  while (low < high)
    {
      bfd_size_type mid = (low + high) / 2;
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

static struct funcinfo*
find_best_matching_function(struct comp_unit *unit, bfd_vma addr, bfd_size_type first, unsigned int number_of_functions)
{
  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;
  
  while (first < number_of_functions)
    {
      if (addr < unit->lookup_funcinfo_table[first].low_addr)
        break;
        
      struct funcinfo *funcinfo = unit->lookup_funcinfo_table[first].funcinfo;
      
      for (struct arange *arange = &funcinfo->arange; arange; arange = arange->next)
        {
          if (!is_address_in_range(addr, arange->low, arange->high))
            continue;
            
          if (is_better_fit(arange, best_fit_len, funcinfo, best_fit))
            {
              best_fit = funcinfo;
              best_fit_len = get_range_length(arange);
            }
        }
      
      first++;
    }
  
  return best_fit;
}

static bool
lookup_address_in_function_table (struct comp_unit *unit,
				  bfd_vma addr,
				  struct funcinfo **function_ptr)
{
  unsigned int number_of_functions = unit->number_of_functions;
  
  if (number_of_functions == 0)
    return false;
    
  if (!build_lookup_funcinfo_table (unit))
    return false;
    
  if (unit->lookup_funcinfo_table[number_of_functions - 1].high_addr < addr)
    return false;
  
  bfd_size_type first = binary_search_first_function(unit, addr, number_of_functions);
  
  struct funcinfo *best_fit = find_best_matching_function(unit, addr, first, number_of_functions);
  
  if (!best_fit)
    return false;
    
  *function_ptr = best_fit;
  return true;
}

/* If SYM at ADDR is within function table of UNIT, set FILENAME_PTR
   and LINENUMBER_PTR, and return TRUE.  */

static bool is_addr_in_range(const struct arange *arange, bfd_vma addr)
{
    return addr >= arange->low && addr < arange->high;
}

static bfd_vma get_range_length(const struct arange *arange)
{
    return arange->high - arange->low;
}

static bool is_better_match(const struct funcinfo *func, 
                           const struct arange *arange,
                           bfd_vma addr,
                           const char *name,
                           bfd_vma best_fit_len)
{
    if (!is_addr_in_range(arange, addr))
        return false;
    
    if (get_range_length(arange) >= best_fit_len)
        return false;
    
    if (!func->file || !func->name)
        return false;
    
    return strstr(name, func->name) != NULL;
}

static struct funcinfo* find_best_matching_function(struct comp_unit *unit,
                                                    bfd_vma addr,
                                                    const char *name)
{
    struct funcinfo *best_fit = NULL;
    bfd_vma best_fit_len = (bfd_vma) -1;
    
    for (struct funcinfo *each = unit->function_table; each; each = each->prev_func)
    {
        for (struct arange *arange = &each->arange; arange; arange = arange->next)
        {
            if (is_better_match(each, arange, addr, name, best_fit_len))
            {
                best_fit = each;
                best_fit_len = get_range_length(arange);
            }
        }
    }
    
    return best_fit;
}

static bool lookup_symbol_in_function_table(struct comp_unit *unit,
                                           asymbol *sym,
                                           bfd_vma addr,
                                           const char **filename_ptr,
                                           unsigned int *linenumber_ptr)
{
    const char *name = bfd_asymbol_name(sym);
    struct funcinfo *best_fit = find_best_matching_function(unit, addr, name);
    
    if (!best_fit)
        return false;
    
    *filename_ptr = best_fit->file;
    *linenumber_ptr = best_fit->line;
    return true;
}

/* Variable table functions.  */

/* If SYM is within variable table of UNIT, set FILENAME_PTR and
   LINENUMBER_PTR, and return TRUE.  */

static bool
lookup_symbol_in_variable_table (struct comp_unit *unit,
				 asymbol *sym,
				 bfd_vma addr,
				 const char **filename_ptr,
				 unsigned int *linenumber_ptr)
{
  const char *name = bfd_asymbol_name (sym);
  struct varinfo* matching_var = NULL;

  for (struct varinfo* each = unit->variable_table; each; each = each->prev_var)
    {
      if (each->addr != addr)
        continue;
      if (each->stack)
        continue;
      if (each->file == NULL)
        continue;
      if (each->name == NULL)
        continue;
      if (strstr (name, each->name) == NULL)
        continue;
      
      matching_var = each;
      break;
    }

  if (matching_var == NULL)
    return false;

  *filename_ptr = matching_var->file;
  *linenumber_ptr = matching_var->line;
  return true;
}

static struct comp_unit *stash_comp_unit (struct dwarf2_debug *,
					  struct dwarf2_debug_file *);
static bool comp_unit_maybe_decode_line_info (struct comp_unit *);

static bool
validate_die_ref(uint64_t die_ref, size_t total)
{
  if (!die_ref || die_ref >= total)
    {
      _bfd_error_handler
        (_("DWARF error: invalid abstract instance DIE ref"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
check_recursion_limit(unsigned int recur_count)
{
  const unsigned int MAX_RECURSION = 100;
  if (recur_count == MAX_RECURSION)
    {
      _bfd_error_handler
        (_("DWARF error: abstract instance recursion detected"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bfd_byte *
get_ref_addr_info_ptr(struct comp_unit *unit, uint64_t die_ref, bfd_byte **info_ptr_end)
{
  bfd_byte *info_ptr;
  size_t total;

  info_ptr = unit->file->dwarf_info_buffer;
  *info_ptr_end = info_ptr + unit->file->dwarf_info_size;
  total = *info_ptr_end - info_ptr;
  
  if (!die_ref)
    return NULL;
  
  if (!validate_die_ref(die_ref, total))
    return NULL;
  
  return info_ptr + die_ref;
}

static bfd_byte *
get_gnu_ref_alt_info_ptr(struct comp_unit *unit, uint64_t die_ref, bfd_byte **info_ptr_end)
{
  bool first_time = unit->stash->alt.dwarf_info_buffer == NULL;
  bfd_byte *info_ptr = read_alt_indirect_ref(unit, die_ref);
  
  if (first_time)
    unit->stash->alt.info_ptr = unit->stash->alt.dwarf_info_buffer;
  
  if (info_ptr == NULL)
    {
      _bfd_error_handler
        (_("DWARF error: unable to read alt ref %" PRIu64), (uint64_t) die_ref);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  
  *info_ptr_end = unit->stash->alt.dwarf_info_buffer + unit->stash->alt.dwarf_info_size;
  return info_ptr;
}

static struct comp_unit *
find_comp_unit_for_die(struct comp_unit *unit, bfd_byte *info_ptr, enum dwarf_form form)
{
  struct comp_unit *u = NULL;
  struct addr_range range = { info_ptr, info_ptr };
  splay_tree_node v = splay_tree_lookup(unit->file->comp_unit_tree, (splay_tree_key)&range);
  
  if (v != NULL)
    u = (struct comp_unit *)v->value;
  
  struct file_info *file_to_search = (form == DW_FORM_ref_addr) ? 
                                     &unit->stash->f : &unit->stash->alt;
  
  while (u == NULL)
    {
      u = stash_comp_unit(unit->stash, file_to_search);
      if (u == NULL)
        break;
      if (info_ptr >= u->info_ptr_unit && info_ptr < u->end_ptr)
        break;
      u = NULL;
    }
  
  return u;
}

static bool
update_unit_for_external_ref(struct comp_unit **unit, bfd_byte *info_ptr, 
                             bfd_byte **info_ptr_end, enum dwarf_form form, uint64_t die_ref)
{
  if (info_ptr >= (*unit)->info_ptr_unit && info_ptr < (*unit)->end_ptr)
    {
      *info_ptr_end = (*unit)->end_ptr;
      return true;
    }
  
  struct comp_unit *u = find_comp_unit_for_die(*unit, info_ptr, form);
  
  if (u == NULL)
    {
      _bfd_error_handler
        (_("DWARF error: unable to locate abstract instance DIE ref %" PRIu64), 
         (uint64_t) die_ref);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  
  *unit = u;
  *info_ptr_end = u->end_ptr;
  return true;
}

static bfd_byte *
get_relative_ref_info_ptr(struct comp_unit *unit, uint64_t die_ref, bfd_byte **info_ptr_end)
{
  bfd_byte *info_ptr;
  size_t total;
  
  info_ptr = unit->info_ptr_unit;
  *info_ptr_end = unit->end_ptr;
  total = *info_ptr_end - info_ptr;
  
  if (!validate_die_ref(die_ref, total))
    return NULL;
  
  return info_ptr + die_ref;
}

static void
process_name_attribute(const struct attribute *attr, const char **pname, 
                      bool *is_linkage, struct comp_unit *unit)
{
  if (*pname == NULL && is_str_form(attr))
    {
      *pname = attr->u.str;
      if (mangle_style(unit->lang) == 0)
        *is_linkage = true;
    }
}

static void
process_linkage_name_attribute(const struct attribute *attr, const char **pname, bool *is_linkage)
{
  if (is_str_form(attr))
    {
      *pname = attr->u.str;
      *is_linkage = true;
    }
}

static void
process_decl_file_attribute(const struct attribute *attr, struct comp_unit *unit, char **filename_ptr)
{
  if (!comp_unit_maybe_decode_line_info(unit))
    return;
  
  if (is_int_form(attr))
    {
      free(*filename_ptr);
      *filename_ptr = concat_filename(unit->line_table, attr->u.val);
    }
}

static bool
process_attribute(struct attribute *attr, struct comp_unit *unit, 
                  unsigned int recur_count, const char **pname, bool *is_linkage,
                  char **filename_ptr, int *linenumber_ptr)
{
  switch (attr->name)
    {
    case DW_AT_name:
      process_name_attribute(attr, pname, is_linkage, unit);
      break;
      
    case DW_AT_specification:
      if (is_int_form(attr) && 
          !find_abstract_instance(unit, attr, recur_count + 1, pname, 
                                 is_linkage, filename_ptr, linenumber_ptr))
        return false;
      break;
      
    case DW_AT_linkage_name:
    case DW_AT_MIPS_linkage_name:
      process_linkage_name_attribute(attr, pname, is_linkage);
      break;
      
    case DW_AT_decl_file:
      process_decl_file_attribute(attr, unit, filename_ptr);
      break;
      
    case DW_AT_decl_line:
      if (is_int_form(attr))
        *linenumber_ptr = attr->u.val;
      break;
      
    default:
      break;
    }
  return true;
}

static bool
find_abstract_instance(struct comp_unit *unit,
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
  
  if (!check_recursion_limit(recur_count))
    return false;
  
  if (attr_ptr->form == DW_FORM_ref_addr)
    {
      info_ptr = get_ref_addr_info_ptr(unit, die_ref, &info_ptr_end);
      if (info_ptr == NULL && die_ref == 0)
        return true;
      if (info_ptr == NULL)
        return false;
    }
  else if (attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      info_ptr = get_gnu_ref_alt_info_ptr(unit, die_ref, &info_ptr_end);
      if (info_ptr == NULL)
        return false;
      
      if (unit->stash->alt.all_comp_units)
        unit = unit->stash->alt.all_comp_units;
    }
  
  if (attr_ptr->form == DW_FORM_ref_addr || attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      if (!update_unit_for_external_ref(&unit, info_ptr, &info_ptr_end, 
                                        attr_ptr->form, die_ref))
        return false;
    }
  else
    {
      info_ptr = get_relative_ref_info_ptr(unit, die_ref, &info_ptr_end);
      if (info_ptr == NULL)
        return false;
    }
  
  abbrev_number = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
  if (!abbrev_number)
    return true;
  
  abbrev = lookup_abbrev(abbrev_number, unit->abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler
        (_("DWARF error: could not find abbrev number %u"), abbrev_number);
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  
  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      info_ptr = read_attribute(&attr, &abbrev->attrs[i], unit, 
                               info_ptr, info_ptr_end);
      if (info_ptr == NULL)
        break;
      
      if (!process_attribute(&attr, unit, recur_count, pname, is_linkage, 
                            filename_ptr, linenumber_ptr))
        return false;
    }
  
  return true;
}

static bool
ensure_ranges_buffer_loaded(struct comp_unit *unit)
{
    if (!unit->file->dwarf_ranges_buffer)
    {
        if (!read_debug_ranges(unit))
            return false;
    }
    return true;
}

static bool
validate_offset(struct comp_unit *unit, uint64_t offset)
{
    return offset <= unit->file->dwarf_ranges_size;
}

static bool
has_sufficient_data(struct comp_unit *unit, bfd_byte *ranges_ptr, bfd_byte *ranges_end)
{
    return 2u * unit->addr_size <= (size_t)(ranges_end - ranges_ptr);
}

static bool
is_end_marker(bfd_vma low_pc, bfd_vma high_pc)
{
    return low_pc == 0 && high_pc == 0;
}

static bool
is_base_address_update(bfd_vma low_pc, bfd_vma high_pc)
{
    return low_pc == (bfd_vma)-1 && high_pc != (bfd_vma)-1;
}

static bool
process_range_entry(struct comp_unit *unit, struct arange *arange,
                   struct trie_node **trie_root, bfd_vma *base_address,
                   bfd_vma low_pc, bfd_vma high_pc)
{
    if (is_base_address_update(low_pc, high_pc))
    {
        *base_address = high_pc;
        return true;
    }
    
    return arange_add(unit, arange, trie_root,
                     *base_address + low_pc, *base_address + high_pc);
}

static bool
read_ranges(struct comp_unit *unit, struct arange *arange,
           struct trie_node **trie_root, uint64_t offset)
{
    bfd_byte *ranges_ptr;
    bfd_byte *ranges_end;
    bfd_vma base_address = unit->base_address;

    if (!ensure_ranges_buffer_loaded(unit))
        return false;

    if (!validate_offset(unit, offset))
        return false;

    ranges_ptr = unit->file->dwarf_ranges_buffer + offset;
    ranges_end = unit->file->dwarf_ranges_buffer + unit->file->dwarf_ranges_size;

    for (;;)
    {
        bfd_vma low_pc;
        bfd_vma high_pc;

        if (!has_sufficient_data(unit, ranges_ptr, ranges_end))
            return false;

        low_pc = read_address(unit, &ranges_ptr, ranges_end);
        high_pc = read_address(unit, &ranges_ptr, ranges_end);

        if (is_end_marker(low_pc, high_pc))
            break;

        if (!process_range_entry(unit, arange, trie_root, &base_address, low_pc, high_pc))
            return false;
    }
    return true;
}

static bool
ensure_rnglists_buffer_loaded(struct comp_unit *unit)
{
    if (!unit->file->dwarf_rnglists_buffer)
        return read_debug_rnglists(unit);
    return true;
}

static bool
validate_buffer_bounds(bfd_byte *ptr, bfd_byte *buffer_start, bfd_byte *buffer_end)
{
    return ptr >= buffer_start && ptr < buffer_end;
}

static bool
check_address_size_available(struct comp_unit *unit, bfd_byte *ptr, bfd_byte *end, size_t multiplier)
{
    return (multiplier * unit->addr_size) <= (size_t)(end - ptr);
}

static bfd_vma
read_leb128_offset(bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
    return _bfd_safe_read_leb128(abfd, ptr, false, end);
}

static bool
process_base_address(struct comp_unit *unit, bfd_byte **rngs_ptr, bfd_byte *rngs_end, bfd_vma *base_address)
{
    if (!check_address_size_available(unit, *rngs_ptr, rngs_end, 1))
        return false;
    *base_address = read_address(unit, rngs_ptr, rngs_end);
    return true;
}

static bool
process_start_length(struct comp_unit *unit, bfd_byte **rngs_ptr, bfd_byte *rngs_end, bfd_vma *low_pc, bfd_vma *high_pc)
{
    if (!check_address_size_available(unit, *rngs_ptr, rngs_end, 1))
        return false;
    *low_pc = read_address(unit, rngs_ptr, rngs_end);
    *high_pc = *low_pc + read_leb128_offset(unit->abfd, rngs_ptr, rngs_end);
    return true;
}

static bool
process_offset_pair(struct comp_unit *unit, bfd_byte **rngs_ptr, bfd_byte *rngs_end, bfd_vma base_address, bfd_vma *low_pc, bfd_vma *high_pc)
{
    *low_pc = base_address + read_leb128_offset(unit->abfd, rngs_ptr, rngs_end);
    *high_pc = base_address + read_leb128_offset(unit->abfd, rngs_ptr, rngs_end);
    return true;
}

static bool
process_start_end(struct comp_unit *unit, bfd_byte **rngs_ptr, bfd_byte *rngs_end, bfd_vma *low_pc, bfd_vma *high_pc)
{
    if (!check_address_size_available(unit, *rngs_ptr, rngs_end, 2))
        return false;
    *low_pc = read_address(unit, rngs_ptr, rngs_end);
    *high_pc = read_address(unit, rngs_ptr, rngs_end);
    return true;
}

static bool
process_range_entry(struct comp_unit *unit, bfd_byte **rngs_ptr, bfd_byte *rngs_end, 
                   bfd_vma *base_address, struct arange *arange, struct trie_node **trie_root)
{
    bfd_vma low_pc = 0;
    bfd_vma high_pc = 0;
    bool add_range = false;
    
    if (*rngs_ptr >= rngs_end)
        return false;
    
    enum dwarf_range_list_entry rlet = read_1_byte(unit->abfd, rngs_ptr, rngs_end);
    
    switch (rlet) {
    case DW_RLE_end_of_list:
        return true;
        
    case DW_RLE_base_address:
        return process_base_address(unit, rngs_ptr, rngs_end, base_address);
        
    case DW_RLE_start_length:
        if (!process_start_length(unit, rngs_ptr, rngs_end, &low_pc, &high_pc))
            return false;
        add_range = true;
        break;
        
    case DW_RLE_offset_pair:
        if (!process_offset_pair(unit, rngs_ptr, rngs_end, *base_address, &low_pc, &high_pc))
            return false;
        add_range = true;
        break;
        
    case DW_RLE_start_end:
        if (!process_start_end(unit, rngs_ptr, rngs_end, &low_pc, &high_pc))
            return false;
        add_range = true;
        break;
        
    case DW_RLE_base_addressx:
    case DW_RLE_startx_endx:
    case DW_RLE_startx_length:
    default:
        return false;
    }
    
    if (add_range && !arange_add(unit, arange, trie_root, low_pc, high_pc))
        return false;
    
    return true;
}

static bool
read_rnglists(struct comp_unit *unit, struct arange *arange,
              struct trie_node **trie_root, uint64_t offset)
{
    bfd_byte *rngs_ptr;
    bfd_byte *rngs_end;
    bfd_vma base_address = unit->base_address;
    
    if (!ensure_rnglists_buffer_loaded(unit))
        return false;
    
    rngs_ptr = unit->file->dwarf_rnglists_buffer + offset;
    if (!validate_buffer_bounds(rngs_ptr, unit->file->dwarf_rnglists_buffer, 
                                unit->file->dwarf_rnglists_buffer + unit->file->dwarf_rnglists_size))
        return false;
    
    rngs_end = unit->file->dwarf_rnglists_buffer + unit->file->dwarf_rnglists_size;
    
    for (;;) {
        bool result = process_range_entry(unit, &rngs_ptr, rngs_end, &base_address, arange, trie_root);
        if (result)
            return true;
        if (rngs_ptr >= rngs_end)
            return false;
    }
}

static bool
read_rangelist (struct comp_unit *unit, struct arange *arange,
		struct trie_node **trie_root, uint64_t offset)
{
  if (unit->version <= 4)
    return read_ranges (unit, arange, trie_root, offset);
  else
    return read_rnglists (unit, arange, trie_root, offset);
}

static struct funcinfo *
lookup_func_by_offset (uint64_t offset, struct funcinfo * table)
{
  for (; table != NULL; table = table->prev_func)
    if (table->unit_offset == offset)
      return table;
  return NULL;
}

static struct varinfo *
lookup_var_by_offset (uint64_t offset, struct varinfo * table)
{
  while (table)
    {
      if (table->unit_offset == offset)
	return table;
      table = table->prev_var;
    }

  return NULL;
}


/* DWARF2 Compilation unit functions.  */

static struct funcinfo *
reverse_funcinfo_list (struct funcinfo *head)
{
  struct funcinfo *reversed = NULL;
  struct funcinfo *current = head;
  
  while (current != NULL)
    {
      struct funcinfo *next = current->prev_func;
      current->prev_func = reversed;
      reversed = current;
      current = next;
    }
  return reversed;
}

static struct varinfo *
reverse_varinfo_list (struct varinfo *head)
{
  struct varinfo *rhead = NULL;
  struct varinfo *temp;

  while (head)
    {
      temp = head->prev_var;
      head->prev_var = rhead;
      rhead = head;
      head = temp;
    }
  return rhead;
}

/* Scan over each die in a comp. unit looking for functions to add
   to the function table and variables to the variable table.  */

static bool
process_die_attributes(struct comp_unit *unit, struct abbrev_info *abbrev,
                       bfd_byte **info_ptr_ptr, bfd_byte *info_ptr_end,
                       struct funcinfo *func, struct varinfo *var,
                       bfd_vma *low_pc, bfd_vma *high_pc, bool *high_pc_relative)
{
    unsigned int i;
    for (i = 0; i < abbrev->num_attrs; ++i)
    {
        struct attribute attr;
        *info_ptr_ptr = read_attribute(&attr, &abbrev->attrs[i],
                                      unit, *info_ptr_ptr, info_ptr_end);
        if (*info_ptr_ptr == NULL)
            return false;

        if (func)
        {
            if (!process_func_attribute(unit, func, &attr, low_pc, high_pc, high_pc_relative))
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
                       struct attribute *attr, bfd_vma *low_pc, bfd_vma *high_pc,
                       bool *high_pc_relative)
{
    switch (attr->name)
    {
    case DW_AT_call_file:
        if (is_int_form(attr))
        {
            free(func->caller_file);
            func->caller_file = concat_filename(unit->line_table, attr->u.val);
        }
        break;
    case DW_AT_call_line:
        if (is_int_form(attr))
            func->caller_line = attr->u.val;
        break;
    case DW_AT_abstract_origin:
    case DW_AT_specification:
        if (is_int_form(attr) &&
            !find_abstract_instance(unit, attr, 0, &func->name,
                                   &func->is_linkage, &func->file, &func->line))
            return false;
        break;
    case DW_AT_name:
        if (func->name == NULL && is_str_form(attr))
        {
            func->name = attr->u.str;
            if (mangle_style(unit->lang) == 0)
                func->is_linkage = true;
        }
        break;
    case DW_AT_linkage_name:
    case DW_AT_MIPS_linkage_name:
        if (is_str_form(attr))
        {
            func->name = attr->u.str;
            func->is_linkage = true;
        }
        break;
    case DW_AT_low_pc:
        if (is_int_form(attr))
            *low_pc = attr->u.val;
        break;
    case DW_AT_high_pc:
        if (is_int_form(attr))
        {
            *high_pc = attr->u.val;
            *high_pc_relative = attr->form != DW_FORM_addr;
        }
        break;
    case DW_AT_ranges:
        if (is_int_form(attr) &&
            !read_rangelist(unit, &func->arange, &unit->file->trie_root, attr->u.val))
            return false;
        break;
    case DW_AT_decl_file:
        if (is_int_form(attr))
        {
            free(func->file);
            func->file = concat_filename(unit->line_table, attr->u.val);
        }
        break;
    case DW_AT_decl_line:
        if (is_int_form(attr))
            func->line = attr->u.val;
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
        if (is_int_form(attr) && attr->u.val)
        {
            bool is_linkage;
            if (!find_abstract_instance(unit, attr, 0, &var->name,
                                       &is_linkage, &var->file, &var->line))
            {
                _bfd_error_handler(_("DWARF error: could not find "
                                    "variable specification at offset 0x%lx"),
                                  (unsigned long)attr->u.val);
            }
        }
        break;
    case DW_AT_name:
        if (is_str_form(attr))
            var->name = attr->u.str;
        break;
    case DW_AT_decl_file:
        if (is_int_form(attr))
        {
            free(var->file);
            var->file = concat_filename(unit->line_table, attr->u.val);
        }
        break;
    case DW_AT_decl_line:
        if (is_int_form(attr))
            var->line = attr->u.val;
        break;
    case DW_AT_external:
        if (is_int_form(attr) && attr->u.val != 0)
            var->stack = false;
        break;
    case DW_AT_location:
        process_var_location(unit, var, attr);
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
        if (attr->u.blk->data != NULL && *attr->u.blk->data == DW_OP_addr)
        {
            var->stack = false;
            if (attr->u.blk->size == unit->addr_size + 1U)
                var->addr = bfd_get(unit->addr_size * 8, unit->abfd,
                                  attr->u.blk->data + 1);
        }
        break;
    }
}

static bool
is_function_tag(enum dwarf_tag tag)
{
    return tag == DW_TAG_subprogram ||
           tag == DW_TAG_entry_point ||
           tag == DW_TAG_inlined_subroutine;
}

static bool
is_variable_tag(enum dwarf_tag tag)
{
    return tag == DW_TAG_variable || tag == DW_TAG_member;
}

static struct funcinfo *
create_function_entry(struct comp_unit *unit, struct abbrev_info *abbrev,
                     uint64_t current_offset)
{
    size_t amt = sizeof(struct funcinfo);
    struct funcinfo *func = (struct funcinfo *)bfd_zalloc(unit->abfd, amt);
    if (func == NULL)
        return NULL;
    
    func->tag = abbrev->tag;
    func->prev_func = unit->function_table;
    func->unit_offset = current_offset;
    unit->function_table = func;
    unit->number_of_functions++;
    BFD_ASSERT(!unit->cached);
    
    return func;
}

static struct varinfo *
create_variable_entry(struct comp_unit *unit, struct abbrev_info *abbrev,
                     uint64_t current_offset)
{
    size_t amt = sizeof(struct varinfo);
    struct varinfo *var = (struct varinfo *)bfd_zalloc(unit->abfd, amt);
    if (var == NULL)
        return NULL;
    
    var->tag = abbrev->tag;
    var->stack = true;
    var->prev_var = unit->variable_table;
    unit->variable_table = var;
    var->unit_offset = current_offset;
    
    return var;
}

static void
set_inlined_function_caller(struct funcinfo *func, struct nest_funcinfo *nested_funcs,
                           int nesting_level)
{
    if (func->tag == DW_TAG_inlined_subroutine)
    {
        int i;
        for (i = nesting_level; i-- != 0;)
        {
            if (nested_funcs[i].func)
            {
                func->caller_func = nested_funcs[i].func;
                break;
            }
        }
    }
}

static struct nest_funcinfo *
resize_nested_funcs(struct nest_funcinfo *nested_funcs, int *nested_funcs_size)
{
    *nested_funcs_size *= 2;
    return (struct nest_funcinfo *)bfd_realloc(nested_funcs,
                                              *nested_funcs_size * sizeof(*nested_funcs));
}

static bool
handle_missing_abbrev(unsigned int abbrev_number)
{
    static unsigned int previous_failed_abbrev = -1U;
    
    if (abbrev_number != previous_failed_abbrev)
    {
        _bfd_error_handler(_("DWARF error: could not find abbrev number %u"),
                          abbrev_number);
        previous_failed_abbrev = abbrev_number;
    }
    bfd_set_error(bfd_error_bad_value);
    return false;
}

static struct funcinfo *
find_function_for_offset(struct funcinfo *last_func, uint64_t current_offset,
                        struct funcinfo *function_table)
{
    if (last_func && last_func->prev_func &&
        last_func->prev_func->unit_offset == current_offset)
        return last_func->prev_func;
    
    return lookup_func_by_offset(current_offset, function_table);
}

static struct varinfo *
find_variable_for_offset(struct varinfo *last_var, uint64_t current_offset,
                        struct varinfo *variable_table)
{
    if (last_var && last_var->prev_var &&
        last_var->prev_var->unit_offset == current_offset)
        return last_var->prev_var;
    
    return lookup_var_by_offset(current_offset, variable_table);
}

#define INITIAL_NESTED_FUNCS_SIZE 32

static bool
first_pass_scan(struct comp_unit *unit, struct nest_funcinfo **nested_funcs,
               int *nested_funcs_size)
{
    bfd *abfd = unit->abfd;
    bfd_byte *info_ptr = unit->first_child_die_ptr;
    bfd_byte *info_ptr_end = unit->end_ptr;
    int nesting_level = 0;
    
    (*nested_funcs)[nesting_level].func = 0;
    
    while (nesting_level >= 0)
    {
        unsigned int abbrev_number, i;
        struct abbrev_info *abbrev;
        uint64_t current_offset;
        
        if (info_ptr >= info_ptr_end)
            return false;
        
        current_offset = info_ptr - unit->info_ptr_unit;
        abbrev_number = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
        
        if (abbrev_number == 0)
        {
            nesting_level--;
            continue;
        }
        
        abbrev = lookup_abbrev(abbrev_number, unit->abbrevs);
        if (!abbrev)
        {
            handle_missing_abbrev(abbrev_number);
            return false;
        }
        
        if (is_function_tag(abbrev->tag))
        {
            struct funcinfo *func = create_function_entry(unit, abbrev, current_offset);
            if (func == NULL)
                return false;
            
            set_inlined_function_caller(func, *nested_funcs, nesting_level);
            (*nested_funcs)[nesting_level].func = func;
        }
        else
        {
            if (is_variable_tag(abbrev->tag))
            {
                if (create_variable_entry(unit, abbrev, current_offset) == NULL)
                    return false;
            }
            (*nested_funcs)[nesting_level].func = 0;
        }
        
        for (i = 0; i < abbrev->num_attrs; ++i)
        {
            struct attribute attr;
            info_ptr = read_attribute(&attr, &abbrev->attrs[i],
                                    unit, info_ptr, info_ptr_end);
            if (info_ptr == NULL)
                return false;
        }
        
        if (abbrev->has_children)
        {
            nesting_level++;
            if (nesting_level >= *nested_funcs_size)
            {
                struct nest_funcinfo *tmp = resize_nested_funcs(*nested_funcs, nested_funcs_size);
                if (tmp == NULL)
                    return false;
                *nested_funcs = tmp;
            }
            (*nested_funcs)[nesting_level].func = 0;
        }
    }
    
    return true;
}

static bool
second_pass_scan(struct comp_unit *unit)
{
    bfd *abfd = unit->abfd;
    bfd_byte *info_ptr = unit->first_child_die_ptr;
    bfd_byte *info_ptr_end = unit->end_ptr;
    int nesting_level = 0;
    struct funcinfo *last_func = NULL;
    struct varinfo *last_var = NULL;
    
    while (nesting_level >= 0)
    {
        unsigned int abbrev_number;
        struct abbrev_info *abbrev;
        struct funcinfo *func = NULL;
        struct varinfo *var = NULL;
        bfd_vma low_pc = 0;
        bfd_vma high_pc = 0;
        bool high_pc_relative = false;
        uint64_t current_offset;
        
        if (info_ptr >= info_ptr_end)
            return false;
        
        current_offset = info_ptr - unit->info_ptr_unit;
        abbrev_number = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
        
        if (!abbrev_number)
        {
            nesting_level--;
            continue;
        }
        
        abbrev = lookup_abbrev(abbrev_number, unit->abbrevs);
        BFD_ASSERT(abbrev != NULL);
        
        if (is_function_tag(abbrev->tag))
        {
            func = find_function_for_offset(last_func, current_offset, unit->function_table);
            if (func == NULL)
                return false;
            last_func = func;
        }
        else if (is_variable_tag(abbrev->tag))
        {
            var = find_variable_for_offset(last_var, current_offset, unit->variable_table);
            if (var == NULL)
                return false;
            last_var = var;
        }
        
        if (!process_die_attributes(unit, abbrev, &info_ptr, info_ptr_end,
                                   func, var, &low_pc, &high_pc, &high_pc_relative))
            return false;
        
        if (abbrev->has_children)
            nesting_level++;
        
        if (high_pc_relative)
            high_pc += low_pc;
        
        if (func && high_pc != 0)
        {
            if (!arange_add(unit, &func->arange, &unit->file->trie_root,
                          low_pc, high_pc))
                return false;
        }
    }
    
    return true;
}

static bool
scan_unit_for_symbols(struct comp_unit *unit)
{
    struct nest_funcinfo *nested_funcs;
    int nested_funcs_size = INITIAL_NESTED_FUNCS_SIZE;
    bool result = false;
    
    nested_funcs = (struct nest_funcinfo *)
        bfd_malloc(nested_funcs_size * sizeof(*nested_funcs));
    if (nested_funcs == NULL)
        return false;
    
    if (!first_pass_scan(unit, &nested_funcs, &nested_funcs_size))
        goto fail;
    
    unit->function_table = reverse_funcinfo_list(unit->function_table);
    unit->variable_table = reverse_varinfo_list(unit->variable_table);
    
    if (!second_pass_scan(unit))
        goto fail;
    
    unit->function_table = reverse_funcinfo_list(unit->function_table);
    unit->variable_table = reverse_varinfo_list(unit->variable_table);
    
    result = true;
    
fail:
    free(nested_funcs);
    return result;
}

/* Read the attributes of the form strx and addrx.  */

static void process_indexed_forms(struct attribute *attr, struct comp_unit *unit)
{
    if (is_strx_form(attr->form))
        attr->u.str = (char *) read_indexed_string(attr->u.val, unit);
    if (is_addrx_form(attr->form))
        attr->u.val = read_indexed_address(attr->u.val, unit);
}

static void handle_stmt_list(struct attribute *attr, struct comp_unit *unit)
{
    unit->stmtlist = 1;
    unit->line_offset = attr->u.val;
}

static void handle_name(struct attribute *attr, struct comp_unit *unit)
{
    if (is_str_form(attr))
        unit->name = attr->u.str;
}

static void handle_low_pc(struct attribute *attr, struct comp_unit *unit, 
                          bfd_vma *low_pc, bool compunit)
{
    *low_pc = attr->u.val;
    if (compunit)
        unit->base_address = *low_pc;
}

static void handle_high_pc(struct attribute *attr, bfd_vma *high_pc, 
                           bool *high_pc_relative)
{
    *high_pc = attr->u.val;
    *high_pc_relative = attr->form != DW_FORM_addr;
}

static void handle_ranges(struct attribute *attr, struct comp_unit *unit)
{
    read_rangelist(unit, &unit->arange, &unit->file->trie_root, attr->u.val);
}

static char* extract_comp_dir(char *comp_dir)
{
    if (!comp_dir)
        return NULL;
    
    char *cp = strchr(comp_dir, ':');
    if (cp && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
        return cp + 1;
    
    return comp_dir;
}

static void handle_comp_dir(struct attribute *attr, struct comp_unit *unit)
{
    char *comp_dir = attr->u.str;
    
    if (!is_str_form(attr))
    {
        _bfd_error_handler(_("DWARF error: DW_AT_comp_dir attribute encountered "
                            "with a non-string form"));
        comp_dir = NULL;
    }
    
    unit->comp_dir = extract_comp_dir(comp_dir);
}

static void handle_language(struct attribute *attr, struct comp_unit *unit)
{
    unit->lang = attr->u.val;
}

static void
reread_attribute(struct comp_unit *unit,
                struct attribute *attr,
                bfd_vma *low_pc,
                bfd_vma *high_pc,
                bool *high_pc_relative,
                bool compunit)
{
    process_indexed_forms(attr, unit);
    
    switch (attr->name)
    {
    case DW_AT_stmt_list:
        handle_stmt_list(attr, unit);
        break;
        
    case DW_AT_name:
        handle_name(attr, unit);
        break;
        
    case DW_AT_low_pc:
        handle_low_pc(attr, unit, low_pc, compunit);
        break;
        
    case DW_AT_high_pc:
        handle_high_pc(attr, high_pc, high_pc_relative);
        break;
        
    case DW_AT_ranges:
        handle_ranges(attr, unit);
        break;
        
    case DW_AT_comp_dir:
        handle_comp_dir(attr, unit);
        break;
        
    case DW_AT_language:
        handle_language(attr, unit);
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

#define INITIAL_STR_ALLOC 200
#define STR_ALLOC_MULTIPLIER 2
#define MIN_DWARF_VERSION 2
#define MAX_DWARF_VERSION 5
#define VALID_OFFSET_SIZE_4 4
#define VALID_OFFSET_SIZE_8 8
#define VALID_ADDR_SIZE_2 2
#define VALID_ADDR_SIZE_4 4
#define VALID_ADDR_SIZE_8 8
#define DWO_ID_SIZE 8
#define TYPE_SIGNATURE_SIZE 8

static bool validate_version(unsigned int version)
{
  if (version < MIN_DWARF_VERSION || version > MAX_DWARF_VERSION)
    {
      if (version)
        {
          _bfd_error_handler
            (_("DWARF error: found dwarf version '%u', this reader"
               " only handles version 2, 3, 4 and 5 information"), version);
          bfd_set_error (bfd_error_bad_value);
        }
      return false;
    }
  return true;
}

static bool validate_addr_size(unsigned int addr_size)
{
  if (addr_size > sizeof (bfd_vma))
    {
      _bfd_error_handler
        (_("DWARF error: found address size '%u', this reader"
           " can not handle sizes greater than '%u'"),
         addr_size,
         (unsigned int) sizeof (bfd_vma));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (addr_size != VALID_ADDR_SIZE_2 && addr_size != VALID_ADDR_SIZE_4 && addr_size != VALID_ADDR_SIZE_8)
    {
      _bfd_error_handler
        ("DWARF error: found address size '%u', this reader"
         " can only handle address sizes '2', '4' and '8'", addr_size);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static void skip_unit_type_fields(enum dwarf_unit_type unit_type, bfd_byte **info_ptr, unsigned int offset_size)
{
  switch (unit_type)
    {
    case DW_UT_type:
      *info_ptr += TYPE_SIGNATURE_SIZE;
      *info_ptr += offset_size;
      break;

    case DW_UT_skeleton:
      *info_ptr += DWO_ID_SIZE;
      break;

    default:
      break;
    }
}

static bool read_version_and_unit_info(bfd *abfd, bfd_byte **info_ptr, bfd_byte *end_ptr,
                                       unsigned int *version, enum dwarf_unit_type *unit_type,
                                       unsigned int *addr_size)
{
  *version = read_2_bytes (abfd, info_ptr, end_ptr);
  if (!validate_version(*version))
    return false;

  if (*version < MAX_DWARF_VERSION)
    *unit_type = DW_UT_compile;
  else
    {
      *unit_type = read_1_byte (abfd, info_ptr, end_ptr);
      *addr_size = read_1_byte (abfd, info_ptr, end_ptr);
    }
  return true;
}

static uint64_t read_abbrev_offset(bfd *abfd, bfd_byte **info_ptr, bfd_byte *end_ptr, unsigned int offset_size)
{
  BFD_ASSERT (offset_size == VALID_OFFSET_SIZE_4 || offset_size == VALID_OFFSET_SIZE_8);
  if (offset_size == VALID_OFFSET_SIZE_4)
    return read_4_bytes (abfd, info_ptr, end_ptr);
  else
    return read_8_bytes (abfd, info_ptr, end_ptr);
}

static struct abbrev_info* read_and_validate_abbrev(bfd *abfd, bfd_byte **info_ptr, bfd_byte *end_ptr,
                                                    struct abbrev_info **abbrevs, unsigned int *abbrev_number)
{
  *abbrev_number = _bfd_safe_read_leb128 (abfd, info_ptr, false, end_ptr);
  if (!*abbrev_number)
    return NULL;

  struct abbrev_info *abbrev = lookup_abbrev (*abbrev_number, abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"), *abbrev_number);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return abbrev;
}

static struct comp_unit* allocate_comp_unit(bfd *abfd, unsigned int version, unsigned int addr_size,
                                           unsigned int offset_size, struct abbrev_info **abbrevs,
                                           bfd_byte *end_ptr, struct dwarf2_debug *stash,
                                           struct dwarf2_debug_file *file, bfd_byte *info_ptr_unit)
{
  size_t amt = sizeof (struct comp_unit);
  struct comp_unit *unit = (struct comp_unit *) bfd_zalloc (abfd, amt);
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
  return unit;
}

static bool should_defer_attribute(struct comp_unit *unit, struct attribute *attr)
{
  return (unit->dwarf_str_offset == 0 && is_strx_form (attr->form))
      || (unit->dwarf_addr_offset == 0 && is_addrx_form (attr->form));
}

static bool grow_str_array(struct attribute **str_addrp, size_t *str_alloc, size_t str_count)
{
  if (str_count <= *str_alloc)
    {
      *str_alloc = STR_ALLOC_MULTIPLIER * (*str_alloc) + INITIAL_STR_ALLOC;
      struct attribute *temp = bfd_realloc (*str_addrp, (*str_alloc) * sizeof (**str_addrp));
      if (temp == NULL)
        return false;
      *str_addrp = temp;
    }
  return true;
}

static void process_stmt_list_attr(struct comp_unit *unit, struct attribute *attr)
{
  if (is_int_form (attr))
    {
      unit->stmtlist = 1;
      unit->line_offset = attr->u.val;
    }
}

static void process_name_attr(struct comp_unit *unit, struct attribute *attr)
{
  if (is_str_form (attr))
    unit->name = attr->u.str;
}

static void process_low_pc_attr(struct comp_unit *unit, struct attribute *attr, bfd_vma *low_pc, bool compunit_flag)
{
  if (is_int_form (attr))
    {
      *low_pc = attr->u.val;
      if (compunit_flag)
        unit->base_address = *low_pc;
    }
}

static void process_high_pc_attr(struct attribute *attr, bfd_vma *high_pc, bool *high_pc_relative)
{
  if (is_int_form (attr))
    {
      *high_pc = attr->u.val;
      *high_pc_relative = attr->form != DW_FORM_addr;
    }
}

static bool process_ranges_attr(struct comp_unit *unit, struct attribute *attr)
{
  if (is_int_form (attr))
    return read_rangelist (unit, &unit->arange, &unit->file->trie_root, attr->u.val);
  return true;
}

static void process_comp_dir_attr(struct comp_unit *unit, struct attribute *attr)
{
  char *comp_dir = attr->u.str;

  if (!is_str_form (attr))
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
}

static void process_language_attr(struct comp_unit *unit, struct attribute *attr)
{
  if (is_int_form (attr))
    unit->lang = attr->u.val;
}

static bool process_attribute(struct comp_unit *unit, struct attribute *attr, bfd_vma *low_pc, 
                             bfd_vma *high_pc, bool *high_pc_relative, bool compunit_flag)
{
  switch (attr->name)
    {
    case DW_AT_stmt_list:
      process_stmt_list_attr(unit, attr);
      break;

    case DW_AT_name:
      process_name_attr(unit, attr);
      break;

    case DW_AT_low_pc:
      process_low_pc_attr(unit, attr, low_pc, compunit_flag);
      break;

    case DW_AT_high_pc:
      process_high_pc_attr(attr, high_pc, high_pc_relative);
      break;

    case DW_AT_ranges:
      if (!process_ranges_attr(unit, attr))
        return false;
      break;

    case DW_AT_comp_dir:
      process_comp_dir_attr(unit, attr);
      break;

    case DW_AT_language:
      process_language_attr(unit, attr);
      break;

    case DW_AT_addr_base:
      unit->dwarf_addr_offset = attr->u.val;
      break;

    case DW_AT_str_offsets_base:
      unit->dwarf_str_offset = attr->u.val;
      break;

    default:
      break;
    }
  return true;
}

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
  unsigned int addr_size = -1;
  struct abbrev_info** abbrevs;
  unsigned int abbrev_number, i;
  struct abbrev_info *abbrev;
  struct attribute attr;
  bfd_byte *end_ptr = info_ptr + unit_length;
  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bfd *abfd = file->bfd_ptr;
  bool high_pc_relative = false;
  enum dwarf_unit_type unit_type;
  struct attribute *str_addrp = NULL;
  size_t str_count = 0;
  size_t str_alloc = 0;
  bool compunit_flag = false;

  if (!read_version_and_unit_info(abfd, &info_ptr, end_ptr, &version, &unit_type, &addr_size))
    return NULL;

  abbrev_offset = read_abbrev_offset(abfd, &info_ptr, end_ptr, offset_size);

  if (version < MAX_DWARF_VERSION)
    addr_size = read_1_byte (abfd, &info_ptr, end_ptr);

  skip_unit_type_fields(unit_type, &info_ptr, offset_size);

  if (!validate_addr_size(addr_size))
    return NULL;

  abbrevs = read_abbrevs (abfd, abbrev_offset, stash, file);
  if (!abbrevs)
    return NULL;

  abbrev = read_and_validate_abbrev(abfd, &info_ptr, end_ptr, abbrevs, &abbrev_number);
  if (!abbrev)
    return NULL;

  unit = allocate_comp_unit(abfd, version, addr_size, offset_size, abbrevs, end_ptr, stash, file, info_ptr_unit);
  if (unit == NULL)
    return NULL;

  if (abbrev->tag == DW_TAG_compile_unit)
    compunit_flag = true;

  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit, info_ptr, end_ptr);
      if (info_ptr == NULL)
        goto err_exit;

      if (should_defer_attribute(unit, &attr))
        {
          if (!grow_str_array(&str_addrp, &str_alloc, str_count))
            goto err_exit;
          str_addrp[str_count] = attr;
          str_count++;
          continue;
        }

      if (!process_attribute(unit, &attr, &low_pc, &high_pc, &high_pc_relative, compunit_flag))
        goto err_exit;
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

  if (unit->error)
    return false;

  if (unit->arange.high == 0 || unit->line_table == NULL)
    return true;

  for (arange = &unit->arange; arange != NULL; arange = arange->next)
    if (addr >= arange->low && addr < arange->high)
      return true;

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
  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  *function_ptr = NULL;
  bool func_p = lookup_address_in_function_table (unit, addr, function_ptr);

  if (func_p && (*function_ptr)->tag == DW_TAG_inlined_subroutine)
    unit->stash->inliner_chain = *function_ptr;

  bool line_p = lookup_address_in_line_info_table (unit->line_table, addr,
                                                    filename_ptr,
                                                    linenumber_ptr,
                                                    discriminator_ptr);
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

  if (unit->first_child_die_ptr < unit->end_ptr
      && !scan_unit_for_symbols (unit))
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
  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  if (sym->flags & BSF_FUNCTION)
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
should_skip_function(struct funcinfo *func)
{
  return func->name == NULL;
}

static bool
should_skip_variable(struct varinfo *var)
{
  return var->stack || var->file == NULL || var->name == NULL;
}

static bool
process_function_list(struct comp_unit *unit,
                     struct info_hash_table *funcinfo_hash_table)
{
  struct funcinfo *each_func;
  bool okay = true;
  
  unit->function_table = reverse_funcinfo_list(unit->function_table);
  
  for (each_func = unit->function_table;
       each_func && okay;
       each_func = each_func->prev_func)
    {
      if (!should_skip_function(each_func))
        okay = insert_info_hash_table(funcinfo_hash_table, each_func->name,
                                      (void*)each_func, false);
    }
  
  unit->function_table = reverse_funcinfo_list(unit->function_table);
  return okay;
}

static bool
process_variable_list(struct comp_unit *unit,
                     struct info_hash_table *varinfo_hash_table)
{
  struct varinfo *each_var;
  bool okay = true;
  
  unit->variable_table = reverse_varinfo_list(unit->variable_table);
  
  for (each_var = unit->variable_table;
       each_var && okay;
       each_var = each_var->prev_var)
    {
      if (!should_skip_variable(each_var))
        okay = insert_info_hash_table(varinfo_hash_table, each_var->name,
                                      (void*)each_var, false);
    }
  
  unit->variable_table = reverse_varinfo_list(unit->variable_table);
  return okay;
}

static bool
comp_unit_hash_info(struct dwarf2_debug *stash,
                   struct comp_unit *unit,
                   struct info_hash_table *funcinfo_hash_table,
                   struct info_hash_table *varinfo_hash_table)
{
  BFD_ASSERT(stash->info_hash_status != STASH_INFO_HASH_DISABLED);
  
  if (!comp_unit_maybe_decode_line_info(unit))
    return false;
  
  BFD_ASSERT(!unit->cached);
  
  if (!process_function_list(unit, funcinfo_hash_table))
    return false;
  
  if (!process_variable_list(unit, varinfo_hash_table))
    return false;
  
  unit->cached = true;
  return true;
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

static bool
section_has_valid_contents(asection *section)
{
  return section != NULL && (section->flags & SEC_HAS_CONTENTS) != 0;
}

static asection *
find_section_by_name(bfd *abfd, const char *name)
{
  asection *section = bfd_get_section_by_name(abfd, name);
  return section_has_valid_contents(section) ? section : NULL;
}

static asection *
find_debug_section_from_start(bfd *abfd, const struct dwarf_debug_section *debug_sections)
{
  asection *msec = find_section_by_name(abfd, debug_sections[debug_info].uncompressed_name);
  if (msec != NULL)
    return msec;
  
  return find_section_by_name(abfd, debug_sections[debug_info].compressed_name);
}

static asection *
find_gnu_linkonce_section(asection *start_section)
{
  asection *msec;
  for (msec = start_section; msec != NULL; msec = msec->next)
  {
    if (section_has_valid_contents(msec) && startswith(msec->name, GNU_LINKONCE_INFO))
      return msec;
  }
  return NULL;
}

static bool
section_matches_debug_name(asection *section, const struct dwarf_debug_section *debug_sections)
{
  const char *uncompressed = debug_sections[debug_info].uncompressed_name;
  const char *compressed = debug_sections[debug_info].compressed_name;
  
  return (strcmp(section->name, uncompressed) == 0) ||
         (compressed != NULL && strcmp(section->name, compressed) == 0);
}

static asection *
find_matching_section_after(asection *after_sec, const struct dwarf_debug_section *debug_sections)
{
  asection *msec;
  for (msec = after_sec->next; msec != NULL; msec = msec->next)
  {
    if (!section_has_valid_contents(msec))
      continue;
    
    if (section_matches_debug_name(msec, debug_sections))
      return msec;
    
    if (startswith(msec->name, GNU_LINKONCE_INFO))
      return msec;
  }
  return NULL;
}

static asection *
find_debug_info(bfd *abfd, const struct dwarf_debug_section *debug_sections,
                asection *after_sec)
{
  if (after_sec == NULL)
  {
    asection *msec = find_debug_section_from_start(abfd, debug_sections);
    if (msec != NULL)
      return msec;
    
    return find_gnu_linkonce_section(abfd->sections);
  }
  
  return find_matching_section_after(after_sec, debug_sections);
}

/* Transfer VMAs from object file to separate debug file.  */

static void copy_section_attributes(asection *source, asection *dest)
{
    dest->output_section = source->output_section;
    dest->output_offset = source->output_offset;
    dest->vma = source->vma;
}

static int is_debug_section(asection *section)
{
    return (section->flags & SEC_DEBUGGING) != 0;
}

static int sections_have_same_name(asection *s1, asection *s2)
{
    return strcmp(s1->name, s2->name) == 0;
}

static void set_debug_vma(bfd *orig_bfd, bfd *debug_bfd)
{
    asection *s = orig_bfd->sections;
    asection *d = debug_bfd->sections;

    while (s != NULL && d != NULL)
    {
        if (is_debug_section(d))
            break;

        if (sections_have_same_name(s, d))
            copy_section_attributes(s, d);

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
  if (stash->f.bfd_ptr == abfd)
    return;

  if (*sec == NULL)
    {
      *syms = stash->f.syms;
      return;
    }

  find_matching_section(abfd, stash, sec, syms);
}

static void
find_matching_section(bfd *abfd, struct dwarf2_debug *stash,
                      asection **sec, asymbol ***syms)
{
  asection *s = abfd->sections;
  asection *d = stash->f.bfd_ptr->sections;

  while (s != NULL && d != NULL)
    {
      if (has_debug_flag(d))
        break;

      if (is_matching_section(s, d, *sec))
        {
          *sec = d;
          *syms = stash->f.syms;
          break;
        }

      s = s->next;
      d = d->next;
    }
}

static int
has_debug_flag(asection *section)
{
  return (section->flags & SEC_DEBUGGING) != 0;
}

static int
is_matching_section(asection *s, asection *d, asection *target)
{
  return s == target && strcmp(s->name, d->name) == 0;
}

/* Unset vmas for adjusted sections in STASH.  */

static void
unset_sections (struct dwarf2_debug *stash)
{
  int i;
  struct adjusted_section *p;

  i = stash->adjusted_section_count;
  p = stash->adjusted_sections;
  for (; i > 0; i--, p++)
    p->section->vma = p->orig_vma;
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

static bool restore_adjusted_sections(struct dwarf2_debug *stash)
{
    struct adjusted_section *p = stash->adjusted_sections;
    int i = stash->adjusted_section_count;
    
    for (; i > 0; i--, p++)
        p->section->vma = p->adj_vma;
    
    return true;
}

static bool should_process_section(asection *sect, bfd *abfd, bfd *orig_bfd, const char *debug_info_name)
{
    if (sect->output_section != NULL
        && sect->output_section != sect
        && (sect->flags & SEC_DEBUGGING) == 0)
        return false;
    
    int is_debug_info = (strcmp(sect->name, debug_info_name) == 0
                        || startswith(sect->name, GNU_LINKONCE_INFO));
    
    if (!((sect->flags & SEC_ALLOC) != 0 && abfd == orig_bfd)
        && !is_debug_info)
        return false;
    
    return true;
}

static int count_sections_to_process(bfd *orig_bfd, struct dwarf2_debug *stash, const char *debug_info_name)
{
    int count = 0;
    bfd *abfd = orig_bfd;
    
    while (1) {
        for (asection *sect = abfd->sections; sect != NULL; sect = sect->next) {
            if (should_process_section(sect, abfd, orig_bfd, debug_info_name))
                count++;
        }
        
        if (abfd == stash->f.bfd_ptr)
            break;
        abfd = stash->f.bfd_ptr;
    }
    
    return count;
}

static bfd_vma align_address(bfd_vma address, asection *sect)
{
    bfd_vma mask = -(bfd_vma) 1 << sect->alignment_power;
    return (address + ~mask) & mask;
}

static void adjust_section(struct adjusted_section *p, asection *sect, 
                          bfd_vma *last_vma, bfd_vma *last_dwarf, 
                          const char *debug_info_name)
{
    bfd_size_type sz = sect->rawsize ? sect->rawsize : sect->size;
    
    p->section = sect;
    p->orig_vma = sect->vma;
    
    int is_debug_info = (strcmp(sect->name, debug_info_name) == 0
                        || startswith(sect->name, GNU_LINKONCE_INFO));
    
    bfd_vma *v = is_debug_info ? last_dwarf : last_vma;
    *v = align_address(*v, sect);
    sect->vma = *v;
    *v += sz;
    
    p->adj_vma = sect->vma;
}

static void process_sections_for_adjustment(bfd *orig_bfd, struct dwarf2_debug *stash,
                                           struct adjusted_section *p, const char *debug_info_name)
{
    bfd_vma last_vma = 0, last_dwarf = 0;
    bfd *abfd = orig_bfd;
    
    while (1) {
        for (asection *sect = abfd->sections; sect != NULL; sect = sect->next) {
            if (!should_process_section(sect, abfd, orig_bfd, debug_info_name))
                continue;
            
            adjust_section(p, sect, &last_vma, &last_dwarf, debug_info_name);
            p++;
        }
        
        if (abfd == stash->f.bfd_ptr)
            break;
        abfd = stash->f.bfd_ptr;
    }
}

#define SINGLE_SECTION_THRESHOLD 1

static bool place_sections(bfd *orig_bfd, struct dwarf2_debug *stash)
{
    if (stash->adjusted_section_count != 0)
        return restore_adjusted_sections(stash);
    
    const char *debug_info_name = stash->debug_sections[debug_info].uncompressed_name;
    int section_count = count_sections_to_process(orig_bfd, stash, debug_info_name);
    
    if (section_count <= SINGLE_SECTION_THRESHOLD) {
        stash->adjusted_section_count = -1;
    } else {
        size_t amt = section_count * sizeof(struct adjusted_section);
        struct adjusted_section *p = (struct adjusted_section *) bfd_malloc(amt);
        
        if (p == NULL)
            return false;
        
        stash->adjusted_sections = p;
        stash->adjusted_section_count = section_count;
        
        process_sections_for_adjustment(orig_bfd, stash, p, debug_info_name);
    }
    
    if (orig_bfd != stash->f.bfd_ptr)
        set_debug_vma(orig_bfd, stash->f.bfd_ptr);
    
    return true;
}

/* Look up a funcinfo by name using the given info hash table.  If found,
   also update the locations pointed to by filename_ptr and linenumber_ptr.

   This function returns TRUE if a funcinfo that matches the given symbol
   and address is found with any error; otherwise it returns FALSE.  */

static bool is_addr_in_range(bfd_vma addr, struct arange *arange)
{
    return addr >= arange->low && addr < arange->high;
}

static bfd_vma get_range_length(struct arange *arange)
{
    return arange->high - arange->low;
}

static bool is_better_fit(struct arange *arange, bfd_vma addr, bfd_vma current_best_len)
{
    return is_addr_in_range(addr, arange) && 
           get_range_length(arange) < current_best_len;
}

static struct funcinfo* find_best_func_for_addr(struct funcinfo *each_func, 
                                                  bfd_vma addr,
                                                  bfd_vma *best_fit_len)
{
    struct funcinfo *best_fit = NULL;
    struct arange *arange;
    
    for (arange = &each_func->arange; arange; arange = arange->next)
    {
        if (is_better_fit(arange, addr, *best_fit_len))
        {
            best_fit = each_func;
            *best_fit_len = get_range_length(arange);
        }
    }
    
    return best_fit;
}

static struct funcinfo* search_func_in_hash_nodes(struct info_list_node *node,
                                                   bfd_vma addr)
{
    struct funcinfo *best_fit = NULL;
    struct funcinfo *current_func;
    bfd_vma best_fit_len = (bfd_vma) -1;
    
    for (; node; node = node->next)
    {
        struct funcinfo *each_func = (struct funcinfo *) node->info;
        current_func = find_best_func_for_addr(each_func, addr, &best_fit_len);
        if (current_func)
        {
            best_fit = current_func;
        }
    }
    
    return best_fit;
}

static bool
info_hash_lookup_funcinfo (struct info_hash_table *hash_table,
                           asymbol *sym,
                           bfd_vma addr,
                           const char **filename_ptr,
                           unsigned int *linenumber_ptr)
{
    const char *name = bfd_asymbol_name (sym);
    struct info_list_node *node = lookup_info_hash_table (hash_table, name);
    struct funcinfo *best_fit = search_func_in_hash_nodes(node, addr);
    
    if (best_fit)
    {
        *filename_ptr = best_fit->file;
        *linenumber_ptr = best_fit->line;
        return true;
    }
    
    return false;
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
  const char *name = bfd_asymbol_name (sym);
  struct info_list_node *node = lookup_info_hash_table (hash_table, name);
  
  while (node)
    {
      struct varinfo* each = (struct varinfo *) node->info;
      if (each->addr == addr)
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

  if (stash->f.all_comp_units == stash->hash_units_head)
    return true;

  each = stash->hash_units_head ? stash->hash_units_head->prev_unit : stash->f.last_comp_unit;

  while (each)
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
  stash->varinfo_hash_table = create_info_hash_table (abfd);
  
  if (!stash->funcinfo_hash_table || !stash->varinfo_hash_table)
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
  BFD_ASSERT (stash->info_hash_status == STASH_INFO_HASH_ON);

  struct info_hash_table *hash_table = (sym->flags & BSF_FUNCTION) 
    ? stash->funcinfo_hash_table 
    : stash->varinfo_hash_table;
    
  info_hash_lookup_func lookup_func = (sym->flags & BSF_FUNCTION)
    ? info_hash_lookup_funcinfo
    : info_hash_lookup_varinfo;
    
  return lookup_func (hash_table, sym, addr, filename_ptr, linenumber_ptr);
}

/* Save current section VMAs.  */

static bool
save_section_vma (const bfd *abfd, struct dwarf2_debug *stash)
{
  if (abfd->section_count == 0)
    return true;
  
  stash->sec_vma = bfd_malloc (sizeof (*stash->sec_vma) * abfd->section_count);
  if (stash->sec_vma == NULL)
    return false;
  
  stash->sec_vma_count = abfd->section_count;
  
  asection *s = abfd->sections;
  for (unsigned int i = 0; s != NULL && i < abfd->section_count; i++, s = s->next)
    {
      stash->sec_vma[i] = (s->output_section != NULL) 
        ? s->output_section->vma + s->output_offset 
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

static bfd_vma
get_section_vma(const asection *s)
{
  if (s->output_section != NULL)
    return s->output_section->vma + s->output_offset;
  return s->vma;
}

static bool
section_vma_same(const bfd *abfd, const struct dwarf2_debug *stash)
{
  asection *s;
  unsigned int i;

  if (abfd->section_count != stash->sec_vma_count)
    return false;

  for (i = 0, s = abfd->sections;
       s != NULL && i < abfd->section_count;
       i++, s = s->next)
    {
      if (get_section_vma(s) != stash->sec_vma[i])
        return false;
    }
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
  bfd_size_type total_size;
  asection *msec;
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;

  if (!initialize_stash(abfd, &stash, pinfo, do_place))
    return false;

  stash->orig_bfd_id = abfd->id;
  stash->debug_sections = debug_sections;
  stash->f.syms = symbols;
  
  if (!setup_stash_tables(abfd, stash))
    return false;

  if (debug_bfd == NULL)
    debug_bfd = abfd;

  msec = find_debug_info(debug_bfd, debug_sections, NULL);
  
  if (msec == NULL && abfd == debug_bfd)
    {
      if (!open_debug_file(abfd, &debug_bfd, &msec, &symbols, stash, debug_sections))
        return false;
    }
  
  stash->f.bfd_ptr = debug_bfd;

  if (do_place && !place_sections(abfd, stash))
    return false;

  if (!load_debug_sections(debug_bfd, debug_sections, msec, symbols, stash, &total_size))
    goto restore_vma;

  stash->f.info_ptr = stash->f.dwarf_info_buffer;
  stash->f.dwarf_info_size = total_size;
  return true;

 restore_vma:
  unset_sections(stash);
  return false;
}

static bool
initialize_stash(bfd *abfd, struct dwarf2_debug **stash, void **pinfo, bool do_place)
{
  if (*stash != NULL)
    {
      if ((*stash)->orig_bfd_id == abfd->id && section_vma_same(abfd, *stash))
        {
          if ((*stash)->f.dwarf_info_size != 0)
            {
              if (do_place && !place_sections(abfd, *stash))
                return false;
              return true;
            }
          return false;
        }
      _bfd_dwarf2_cleanup_debug_info(abfd, pinfo);
      memset(*stash, 0, sizeof(**stash));
    }
  else
    {
      *stash = (struct dwarf2_debug *) bfd_zalloc(abfd, sizeof(**stash));
      if (!*stash)
        return false;
      *pinfo = *stash;
    }
  return true;
}

static bool
setup_stash_tables(bfd *abfd, struct dwarf2_debug *stash)
{
  if (!save_section_vma(abfd, stash))
    return false;

  stash->f.abbrev_offsets = htab_create_alloc(10, hash_abbrev, eq_abbrev,
                                               del_abbrev, calloc, free);
  if (!stash->f.abbrev_offsets)
    return false;

  stash->alt.abbrev_offsets = htab_create_alloc(10, hash_abbrev, eq_abbrev,
                                                 del_abbrev, calloc, free);
  if (!stash->alt.abbrev_offsets)
    return false;

  stash->f.trie_root = alloc_trie_leaf(abfd);
  if (!stash->f.trie_root)
    return false;

  stash->alt.trie_root = alloc_trie_leaf(abfd);
  if (!stash->alt.trie_root)
    return false;

  return true;
}

static bool
open_debug_file(bfd *abfd, bfd **debug_bfd, asection **msec, asymbol ***symbols,
                struct dwarf2_debug *stash, const struct dwarf_debug_section *debug_sections)
{
  char *debug_filename = bfd_follow_build_id_debuglink(abfd, DEBUGDIR);
  if (debug_filename == NULL)
    debug_filename = bfd_follow_gnu_debuglink(abfd, DEBUGDIR);

  if (debug_filename == NULL)
    return false;

  *debug_bfd = bfd_openr(debug_filename, NULL);
  free(debug_filename);
  
  if (*debug_bfd == NULL)
    return false;

  (*debug_bfd)->flags |= BFD_DECOMPRESS;
  
  if (!bfd_check_format(*debug_bfd, bfd_object) ||
      (*msec = find_debug_info(*debug_bfd, debug_sections, NULL)) == NULL ||
      !bfd_generic_link_read_symbols(*debug_bfd))
    {
      bfd_close(*debug_bfd);
      return false;
    }

  *symbols = bfd_get_outsymbols(*debug_bfd);
  stash->f.syms = *symbols;
  stash->close_on_cleanup = true;
  return true;
}

static bool
load_debug_sections(bfd *debug_bfd, const struct dwarf_debug_section *debug_sections,
                    asection *msec, asymbol **symbols, struct dwarf2_debug *stash,
                    bfd_size_type *total_size)
{
  if (!find_debug_info(debug_bfd, debug_sections, msec))
    {
      *total_size = bfd_get_section_limit_octets(debug_bfd, msec);
      return read_section(debug_bfd, &stash->debug_sections[debug_info],
                          symbols, 0, &stash->f.dwarf_info_buffer, total_size);
    }

  if (!calculate_total_size(debug_bfd, debug_sections, total_size))
    return false;

  stash->f.dwarf_info_buffer = (bfd_byte *) bfd_malloc(*total_size);
  if (stash->f.dwarf_info_buffer == NULL)
    return false;

  return read_all_sections(debug_bfd, debug_sections, symbols, stash, total_size);
}

static bool
calculate_total_size(bfd *debug_bfd, const struct dwarf_debug_section *debug_sections,
                     bfd_size_type *total_size)
{
  asection *msec;
  *total_size = 0;
  
  for (msec = find_debug_info(debug_bfd, debug_sections, NULL);
       msec;
       msec = find_debug_info(debug_bfd, debug_sections, msec))
    {
      if (bfd_section_size_insane(debug_bfd, msec))
        return false;
        
      bfd_size_type readsz = bfd_get_section_limit_octets(debug_bfd, msec);
      
      if (*total_size + readsz < *total_size)
        {
          bfd_set_error(bfd_error_no_memory);
          return false;
        }
      *total_size += readsz;
    }
  return true;
}

static bool
read_all_sections(bfd *debug_bfd, const struct dwarf_debug_section *debug_sections,
                  asymbol **symbols, struct dwarf2_debug *stash, bfd_size_type *total_size)
{
  asection *msec;
  *total_size = 0;
  
  for (msec = find_debug_info(debug_bfd, debug_sections, NULL);
       msec;
       msec = find_debug_info(debug_bfd, debug_sections, msec))
    {
      bfd_size_type readsz = bfd_get_section_limit_octets(debug_bfd, msec);
      if (readsz == 0)
        continue;

      if (!bfd_simple_get_relocated_section_contents(debug_bfd, msec, 
                                                      stash->f.dwarf_info_buffer + *total_size,
                                                      symbols))
        return false;

      *total_size += readsz;
    }
  return true;
}

/* Parse the next DWARF2 compilation unit at FILE->INFO_PTR.  */

static unsigned int determine_offset_size(bfd_size_type *length, bfd *bfd_ptr, bfd_byte **info_ptr, bfd_byte *info_ptr_end)
{
  const bfd_size_type DWARF3_64BIT_MARKER = 0xffffffff;
  const bfd_size_type IRIX_64BIT_MARKER = 0;
  const unsigned int OFFSET_SIZE_32 = 4;
  const unsigned int OFFSET_SIZE_64 = 8;

  if (*length == DWARF3_64BIT_MARKER)
    {
      *length = read_8_bytes(bfd_ptr, info_ptr, info_ptr_end);
      return OFFSET_SIZE_64;
    }
  
  if (*length == IRIX_64BIT_MARKER)
    {
      *length = read_4_bytes(bfd_ptr, info_ptr, info_ptr_end);
      return OFFSET_SIZE_64;
    }
  
  return OFFSET_SIZE_32;
}

static void initialize_comp_unit_tree(struct dwarf2_debug_file *file)
{
  if (file->comp_unit_tree == NULL)
    file->comp_unit_tree = splay_tree_new(splay_tree_compare_addr_range,
                                          splay_tree_free_addr_range, NULL);
}

static void insert_comp_unit_to_tree(struct dwarf2_debug_file *file, struct comp_unit *each)
{
  struct addr_range *r = (struct addr_range *)bfd_malloc(sizeof(struct addr_range));
  r->start = each->info_ptr_unit;
  r->end = each->end_ptr;
  
  splay_tree_node v = splay_tree_lookup(file->comp_unit_tree, (splay_tree_key)r);
  if (v != NULL || r->end <= r->start)
    abort();
    
  splay_tree_insert(file->comp_unit_tree, (splay_tree_key)r, (splay_tree_value)each);
}

static void link_comp_unit_to_list(struct dwarf2_debug_file *file, struct comp_unit *each)
{
  if (file->all_comp_units)
    file->all_comp_units->prev_unit = each;
  else
    file->last_comp_unit = each;

  each->next_unit = file->all_comp_units;
  file->all_comp_units = each;
}

static void handle_comp_unit_without_ranges(struct dwarf2_debug_file *file, struct comp_unit *each)
{
  if (each->arange.high == 0)
    {
      each->next_unit_without_ranges = file->all_comp_units_without_ranges;
      file->all_comp_units_without_ranges = each->next_unit_without_ranges;
    }
}

static struct comp_unit *process_comp_unit(struct dwarf2_debug *stash, struct dwarf2_debug_file *file, 
                                           bfd_size_type length, bfd_byte *info_ptr_unit, unsigned int offset_size)
{
  struct comp_unit *each = parse_comp_unit(stash, file, file->info_ptr, length, 
                                           info_ptr_unit, offset_size);
  if (!each)
    return NULL;

  initialize_comp_unit_tree(file);
  insert_comp_unit_to_tree(file, each);
  link_comp_unit_to_list(file, each);
  handle_comp_unit_without_ranges(file, each);
  
  file->info_ptr += length;
  return each;
}

static struct comp_unit *
stash_comp_unit(struct dwarf2_debug *stash, struct dwarf2_debug_file *file)
{
  bfd_byte *info_ptr_unit = file->info_ptr;
  bfd_byte *info_ptr_end = file->dwarf_info_buffer + file->dwarf_info_size;

  if (file->info_ptr >= info_ptr_end)
    return NULL;

  bfd_size_type length = read_4_bytes(file->bfd_ptr, &file->info_ptr, info_ptr_end);
  unsigned int offset_size = determine_offset_size(&length, file->bfd_ptr, &file->info_ptr, info_ptr_end);

  if (length == 0 || length > (size_t)(info_ptr_end - file->info_ptr))
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  struct comp_unit *result = process_comp_unit(stash, file, length, info_ptr_unit, offset_size);
  if (!result)
    file->info_ptr = info_ptr_end;
    
  return result;
}

/* Hash function for an asymbol.  */

static hashval_t
hash_asymbol (const void *sym)
{
  const asymbol *asym = sym;
  return htab_hash_string (asym->name);
}

/* Equality function for asymbols.  */

static int
eq_asymbol (const void *a, const void *b)
{
  const asymbol *sa = a;
  const asymbol *sb = b;
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
  htab_t sym_hash;
  bfd_signed_vma result = 0;

  stash = (struct dwarf2_debug *) *pinfo;

  if (stash == NULL || symbols == NULL)
    return 0;

  sym_hash = create_symbol_hash_table(symbols);
  result = find_first_matching_symbol_bias(stash, sym_hash);
  htab_delete (sym_hash);
  
  return result;
}

static htab_t
create_symbol_hash_table(asymbol ** symbols)
{
  htab_t sym_hash;
  asymbol ** psym;
  
  sym_hash = htab_create_alloc (10, hash_asymbol, eq_asymbol,
				NULL, xcalloc, free);
  
  for (psym = symbols; * psym != NULL; psym++)
    {
      insert_function_symbol(sym_hash, *psym);
    }
  
  return sym_hash;
}

static void
insert_function_symbol(htab_t sym_hash, asymbol * sym)
{
  if (sym->flags & BSF_FUNCTION && sym->section != NULL)
    {
      void **slot = htab_find_slot (sym_hash, sym, INSERT);
      *slot = sym;
    }
}

static bfd_signed_vma
find_first_matching_symbol_bias(struct dwarf2_debug *stash, htab_t sym_hash)
{
  struct comp_unit * unit;
  
  for (unit = stash->f.all_comp_units; unit; unit = unit->next_unit)
    {
      bfd_signed_vma bias = find_unit_symbol_bias(unit, sym_hash);
      if (bias != 0)
        return bias;
    }
  
  return 0;
}

static bfd_signed_vma
find_unit_symbol_bias(struct comp_unit * unit, htab_t sym_hash)
{
  struct funcinfo * func;
  
  comp_unit_maybe_decode_line_info (unit);
  
  for (func = unit->function_table; func != NULL; func = func->prev_func)
    {
      bfd_signed_vma bias = calculate_function_bias(func, sym_hash);
      if (bias != 0)
        return bias;
    }
  
  return 0;
}

static bfd_signed_vma
calculate_function_bias(struct funcinfo * func, htab_t sym_hash)
{
  asymbol search, *sym;
  
  if (!func->name || !func->arange.low)
    return 0;
  
  search.name = func->name;
  sym = htab_find (sym_hash, &search);
  
  if (sym != NULL)
    return func->arange.low - (sym->value + sym->section->vma);
  
  return 0;
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

  initialize_output_parameters(filename_ptr, functionname_ptr, linenumber_ptr, discriminator_ptr);

  if (!_bfd_dwarf2_slurp_debug_info(abfd, NULL, debug_sections, symbols, pinfo,
                                    (abfd->flags & (EXEC_P | DYNAMIC)) == 0))
    return false;

  stash = (struct dwarf2_debug *) *pinfo;

  if (!setup_alternative_file(stash, alt_filename))
    return false;

  do_line = setup_search_parameters(symbol, &section, &addr, &offset, functionname_ptr);
  
  if (!do_line)
    resolve_data_symbol(&symbol, &do_line, abfd, symbols, section, offset);

  addr = calculate_final_address(addr, section);

  if (!stash->f.info_ptr)
    return false;

  stash->inliner_chain = NULL;

  if (do_line)
    found = search_line_info(stash, symbol, addr, filename_ptr, linenumber_ptr, abfd);
  else
    found = search_nearest_line(stash, addr, filename_ptr, &function, 
                               linenumber_ptr, discriminator_ptr);

  if (!found)
    found = search_remaining_units(stash, do_line, symbol, addr, filename_ptr,
                                   &function, linenumber_ptr, discriminator_ptr);

  found = finalize_function_name(found, functionname_ptr, function, symbols, 
                                 abfd, section, offset, filename_ptr, stash);

  unset_sections(stash);
  return found;
}

static void initialize_output_parameters(const char **filename_ptr,
                                        const char **functionname_ptr,
                                        unsigned int *linenumber_ptr,
                                        unsigned int *discriminator_ptr)
{
  *filename_ptr = NULL;
  if (functionname_ptr != NULL)
    *functionname_ptr = NULL;
  *linenumber_ptr = 0;
  if (discriminator_ptr)
    *discriminator_ptr = 0;
}

static bool setup_alternative_file(struct dwarf2_debug *stash, const char *alt_filename)
{
  if (stash->alt.bfd_ptr != NULL || alt_filename == NULL)
    return true;

  bfd *alt_bfd = bfd_openr(alt_filename, NULL);
  if (alt_bfd == NULL)
    return false;

  if (!bfd_check_format(alt_bfd, bfd_object)) {
    bfd_set_error(bfd_error_wrong_format);
    bfd_close(alt_bfd);
    return false;
  }

  stash->alt.bfd_ptr = alt_bfd;
  return true;
}

static bool setup_search_parameters(asymbol *symbol, asection **section,
                                   bfd_vma *addr, bfd_vma *offset,
                                   const char **functionname_ptr)
{
  if (symbol != NULL) {
    BFD_ASSERT(*section == NULL && *offset == 0 && functionname_ptr == NULL);
    *section = bfd_asymbol_section(symbol);
    *addr = symbol->value;
    return true;
  }
  
  BFD_ASSERT(*section != NULL && functionname_ptr != NULL);
  *addr = *offset;
  return false;
}

static void resolve_data_symbol(asymbol **symbol, bool *do_line, bfd *abfd,
                               asymbol **symbols, asection *section, bfd_vma offset)
{
  if (symbols == NULL || (section->flags & SEC_CODE) != 0)
    return;

  asymbol **tmp;
  for (tmp = symbols; (*tmp) != NULL; ++tmp) {
    if ((*tmp)->the_bfd != abfd || (*tmp)->section != section ||
        (*tmp)->value != offset || ((*tmp)->flags & BSF_SECTION_SYM) != 0)
      continue;

    *symbol = *tmp;
    *do_line = true;
    if (((*symbol)->flags & BSF_GLOBAL) != 0)
      break;
  }
}

static bfd_vma calculate_final_address(bfd_vma addr, asection *section)
{
  if (section->output_section)
    return addr + section->output_section->vma + section->output_offset;
  return addr + section->vma;
}

static int search_line_info(struct dwarf2_debug *stash, asymbol *symbol,
                           bfd_vma addr, const char **filename_ptr,
                           unsigned int *linenumber_ptr, bfd *abfd)
{
  int found = false;

  if (stash->info_hash_status == STASH_INFO_HASH_OFF)
    stash_maybe_enable_info_hash_tables(abfd, stash);

  if (stash->info_hash_status == STASH_INFO_HASH_ON)
    stash_maybe_update_info_hash_tables(stash);

  if (stash->info_hash_status == STASH_INFO_HASH_ON) {
    found = stash_find_line_fast(stash, symbol, addr, filename_ptr, linenumber_ptr);
    if (found)
      return found;
  }

  struct comp_unit *each;
  for (each = stash->f.all_comp_units; each; each = each->next_unit) {
    if ((symbol->flags & BSF_FUNCTION) != 0 && 
        !comp_unit_may_contain_address(each, addr))
      continue;

    found = comp_unit_find_line(each, symbol, addr, filename_ptr, linenumber_ptr);
    if (found)
      break;
  }
  return found;
}

static int search_in_trie(struct trie_node *trie, bfd_vma addr, 
                         const char **filename_ptr, struct funcinfo **function,
                         unsigned int *linenumber_ptr, unsigned int *discriminator_ptr)
{
  const int BITS_PER_BYTE = 8;
  const int BYTE_MASK = 0xff;
  unsigned int bits = VMA_BITS - BITS_PER_BYTE;

  while (trie && trie->num_room_in_leaf == 0) {
    int ch = (addr >> bits) & BYTE_MASK;
    trie = ((struct trie_interior *) trie)->children[ch];
    bits -= BITS_PER_BYTE;
  }

  if (!trie)
    return false;

  const struct trie_leaf *leaf = (struct trie_leaf *) trie;
  unsigned int i;

  for (i = 0; i < leaf->num_stored_in_leaf; ++i)
    leaf->ranges[i].unit->mark = false;

  for (i = 0; i < leaf->num_stored_in_leaf; ++i) {
    struct comp_unit *unit = leaf->ranges[i].unit;
    if (unit->mark || addr < leaf->ranges[i].low_pc || 
        addr >= leaf->ranges[i].high_pc)
      continue;

    unit->mark = true;
    if (comp_unit_find_nearest_line(unit, addr, filename_ptr, function,
                                   linenumber_ptr, discriminator_ptr))
      return true;
  }
  return false;
}

static int search_units_without_ranges(struct dwarf2_debug *stash, bfd_vma addr,
                                      const char **filename_ptr, struct funcinfo **function,
                                      unsigned int *linenumber_ptr, unsigned int *discriminator_ptr)
{
  struct comp_unit **prev_each = &stash->f.all_comp_units_without_ranges;
  struct comp_unit *each;

  for (each = *prev_each; each; each = each->next_unit_without_ranges) {
    if (each->arange.high != 0) {
      *prev_each = each->next_unit_without_ranges;
      continue;
    }

    if (comp_unit_find_nearest_line(each, addr, filename_ptr, function,
                                   linenumber_ptr, discriminator_ptr))
      return true;

    prev_each = &each->next_unit_without_ranges;
  }
  return false;
}

static int search_nearest_line(struct dwarf2_debug *stash, bfd_vma addr,
                              const char **filename_ptr, struct funcinfo **function,
                              unsigned int *linenumber_ptr, unsigned int *discriminator_ptr)
{
  int found = search_in_trie(stash->f.trie_root, addr, filename_ptr, 
                            function, linenumber_ptr, discriminator_ptr);
  if (!found)
    found = search_units_without_ranges(stash, addr, filename_ptr,
                                       function, linenumber_ptr, discriminator_ptr);
  return found;
}

static int search_remaining_units(struct dwarf2_debug *stash, bool do_line,
                                 asymbol *symbol, bfd_vma addr, const char **filename_ptr,
                                 struct funcinfo **function, unsigned int *linenumber_ptr,
                                 unsigned int *discriminator_ptr)
{
  struct comp_unit *each;
  int found = false;

  while ((each = stash_comp_unit(stash, &stash->f)) != NULL) {
    if (do_line) {
      if ((symbol->flags & BSF_FUNCTION) != 0 && 
          !comp_unit_may_contain_address(each, addr))
        continue;
      found = comp_unit_find_line(each, symbol, addr, filename_ptr, linenumber_ptr);
    } else {
      if (!comp_unit_may_contain_address(each, addr))
        continue;
      found = comp_unit_find_nearest_line(each, addr, filename_ptr, function,
                                         linenumber_ptr, discriminator_ptr);
    }
    if (found)
      break;
  }
  return found;
}

static int finalize_function_name(int found, const char **functionname_ptr,
                                 struct funcinfo *function, asymbol **symbols,
                                 bfd *abfd, asection *section, bfd_vma offset,
                                 const char **filename_ptr, struct dwarf2_debug *stash)
{
  const int LINKAGE_FOUND = 2;

  if (functionname_ptr && function && function->is_linkage) {
    *functionname_ptr = function->name;
    if (!found)
      return LINKAGE_FOUND;
  } else if (functionname_ptr && (!*functionname_ptr || (function && !function->is_linkage))) {
    found = resolve_function_name(found, functionname_ptr, function, symbols,
                                 abfd, section, offset, filename_ptr, stash);
  }
  return found;
}

static int resolve_function_name(int found, const char **functionname_ptr,
                                struct funcinfo *function, asymbol **symbols,
                                bfd *abfd, asection *section, bfd_vma offset,
                                const char **filename_ptr, struct dwarf2_debug *stash)
{
  const int LINKAGE_FOUND = 2;
  asymbol *fun;
  asymbol **syms = symbols;
  asection *sec = section;

  _bfd_dwarf2_stash_syms(stash, abfd, &sec, &syms);
  fun = _bfd_elf_find_function(abfd, syms, sec, offset,
                               *filename_ptr ? NULL : filename_ptr,
                               functionname_ptr);

  if (!found && fun != NULL)
    found = LINKAGE_FOUND;

  if (function && !function->is_linkage) {
    bfd_vma sec_vma = calculate_section_vma(section);
    if (fun == NULL)
      *functionname_ptr = function->name;
    else if (fun->value + sec_vma == function->arange.low)
      function->name = *functionname_ptr;
    function->is_linkage = true;
  }
  return found;
}

static bfd_vma calculate_section_vma(asection *section)
{
  if (section->output_section != NULL)
    return section->output_section->vma + section->output_offset;
  return section->vma;
}

bool
_bfd_dwarf2_find_inliner_info (bfd *abfd ATTRIBUTE_UNUSED,
			       const char **filename_ptr,
			       const char **functionname_ptr,
			       unsigned int *linenumber_ptr,
			       void **pinfo)
{
  struct dwarf2_debug *stash;
  struct funcinfo *func;

  stash = (struct dwarf2_debug *) *pinfo;
  if (!stash)
    return false;

  func = stash->inliner_chain;
  if (!func || !func->caller_func)
    return false;

  *filename_ptr = func->caller_file;
  *functionname_ptr = func->caller_func->name;
  *linenumber_ptr = func->caller_line;
  stash->inliner_chain = func->caller_func;
  return true;
}

void
_bfd_dwarf2_cleanup_debug_info (bfd *abfd, void **pinfo)
{
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;

  if (abfd == NULL || stash == NULL)
    return;

  _cleanup_hash_tables(stash);
  _cleanup_debug_files(stash);
  _cleanup_stash_resources(stash);
}

static void
_cleanup_hash_tables(struct dwarf2_debug *stash)
{
  if (stash->varinfo_hash_table)
    bfd_hash_table_free (&stash->varinfo_hash_table->base);
  if (stash->funcinfo_hash_table)
    bfd_hash_table_free (&stash->funcinfo_hash_table->base);
}

static void
_cleanup_debug_files(struct dwarf2_debug *stash)
{
  _cleanup_single_file(&stash->f);
  _cleanup_single_file(&stash->alt);
}

static void
_cleanup_single_file(struct dwarf2_debug_file *file)
{
  _cleanup_comp_units(file);
  _cleanup_file_resources(file);
}

static void
_cleanup_comp_units(struct dwarf2_debug_file *file)
{
  struct comp_unit *each;
  
  for (each = file->all_comp_units; each; each = each->next_unit)
    {
      _cleanup_line_table(each, file);
      _cleanup_lookup_table(each);
      _cleanup_function_table(each);
      _cleanup_variable_table(each);
    }
}

static void
_cleanup_line_table(struct comp_unit *unit, struct dwarf2_debug_file *file)
{
  if (unit->line_table && unit->line_table != file->line_table)
    {
      free (unit->line_table->files);
      free (unit->line_table->dirs);
    }
}

static void
_cleanup_lookup_table(struct comp_unit *unit)
{
  free (unit->lookup_funcinfo_table);
  unit->lookup_funcinfo_table = NULL;
}

static void
_cleanup_function_table(struct comp_unit *unit)
{
  struct funcinfo *function_table = unit->function_table;
  
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
_cleanup_variable_table(struct comp_unit *unit)
{
  struct varinfo *variable_table = unit->variable_table;
  
  while (variable_table)
    {
      free (variable_table->file);
      variable_table->file = NULL;
      variable_table = variable_table->prev_var;
    }
}

static void
_cleanup_file_resources(struct dwarf2_debug_file *file)
{
  if (file->line_table)
    {
      free (file->line_table->files);
      free (file->line_table->dirs);
    }
    
  htab_delete (file->abbrev_offsets);
  
  if (file->comp_unit_tree != NULL)
    splay_tree_delete (file->comp_unit_tree);
    
  _free_file_buffers(file);
}

static void
_free_file_buffers(struct dwarf2_debug_file *file)
{
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
_cleanup_stash_resources(struct dwarf2_debug *stash)
{
  free (stash->sec_vma);
  free (stash->adjusted_sections);
  
  if (stash->close_on_cleanup)
    bfd_close (stash->f.bfd_ptr);
    
  if (stash->alt.bfd_ptr)
    bfd_close (stash->alt.bfd_ptr);
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
is_symbol_beyond_offset(bfd_vma code_off, bfd_vma offset)
{
  return code_off > offset;
}

static inline bool
is_symbol_further_from_offset(bfd_vma code_off, bfd_vma cache_code_off)
{
  return code_off < cache_code_off;
}

static inline bool
is_symbol_closer_to_offset(bfd_vma code_off, bfd_vma cache_code_off)
{
  return code_off > cache_code_off;
}

static inline bool
does_symbol_cover_offset(bfd_vma code_off, bfd_size_type code_size, bfd_vma offset)
{
  return code_off + code_size > offset;
}

static inline bool
is_function_symbol(flagword flags)
{
  return (flags & BSF_FUNCTION) != 0;
}

static inline int
get_symbol_type(asymbol *sym)
{
  return ELF_ST_TYPE(((elf_symbol_type *)sym)->internal_elf_sym.st_info);
}

static inline bool
prefer_function_over_non_function(asymbol *cache_func, asymbol *sym)
{
  bool cache_is_function = is_function_symbol(cache_func->flags);
  bool sym_is_function = is_function_symbol(sym->flags);
  
  if (cache_is_function && !sym_is_function)
    return false;
  if (sym_is_function && !cache_is_function)
    return true;
  
  return false;
}

static inline bool
prefer_typed_over_untyped(asymbol *cache_func, asymbol *sym)
{
  int cache_type = get_symbol_type(cache_func);
  int sym_type = get_symbol_type(sym);
  
  if (cache_type == STT_NOTYPE && sym_type != STT_NOTYPE)
    return true;
  if (cache_type != STT_NOTYPE && sym_type == STT_NOTYPE)
    return false;
  
  return false;
}

static inline bool
handle_both_symbols_cover_offset(elf_find_function_cache *cache, asymbol *sym, bfd_size_type code_size)
{
  bool function_preference = prefer_function_over_non_function(cache->func, sym);
  if (function_preference)
    return true;
  
  if (is_function_symbol(cache->func->flags) && !is_function_symbol(sym->flags))
    return false;
  
  bool type_preference = prefer_typed_over_untyped(cache->func, sym);
  if (type_preference)
    return true;
  
  if (get_symbol_type(cache->func) != STT_NOTYPE && get_symbol_type(sym) == STT_NOTYPE)
    return false;
  
  return code_size < cache->code_size;
}

static inline bool
better_fit(elf_find_function_cache *cache,
          asymbol *sym,
          bfd_vma code_off,
          bfd_size_type code_size,
          bfd_vma offset)
{
  if (is_symbol_beyond_offset(code_off, offset))
    return false;
  
  if (is_symbol_further_from_offset(code_off, cache->code_off))
    return false;
  
  if (is_symbol_closer_to_offset(code_off, cache->code_off))
    return true;
  
  if (!does_symbol_cover_offset(cache->code_off, cache->code_size, offset))
    return code_size > cache->code_size;
  
  if (!does_symbol_cover_offset(code_off, code_size, offset))
    return false;
  
  return handle_both_symbols_cover_offset(cache, sym, code_size);
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
  if (symbols == NULL)
    return NULL;

  if (bfd_get_flavour (abfd) != bfd_target_elf_flavour)
    return NULL;

  elf_find_function_cache * cache = elf_tdata (abfd)->elf_find_function_cache;

  if (cache == NULL)
    {
      cache = bfd_zalloc (abfd, sizeof (*cache));
      elf_tdata (abfd)->elf_find_function_cache = cache;
      if (cache == NULL)
	return NULL;
    }

  if (cache->last_section != section
      || cache->func == NULL
      || offset < cache->func->value
      || offset >= cache->func->value + cache->code_size)
    {
      find_best_match_in_symbols(abfd, symbols, section, offset, cache);
    }

  if (cache->func == NULL)
    return NULL;

  if (filename_ptr)
    *filename_ptr = cache->filename;
  if (functionname_ptr)
    *functionname_ptr = bfd_asymbol_name (cache->func);

  return cache->func;
}

static void
find_best_match_in_symbols(bfd *abfd,
			    asymbol **symbols,
			    asection *section,
			    bfd_vma offset,
			    elf_find_function_cache *cache)
{
  asymbol *file;
  asymbol **p;
  enum { nothing_seen, symbol_seen, file_after_symbol_seen } state;
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);

  file = NULL;
  state = nothing_seen;
  cache->filename = NULL;
  cache->func = NULL;
  cache->code_size = 0;
  cache->code_off = 0;
  cache->last_section = section;

  for (p = symbols; *p != NULL; p++)
    {
      process_symbol(*p, &file, &state, bed, section, offset, cache);
    }
}

static void
process_symbol(asymbol *sym,
	       asymbol **file,
	       int *state,
	       const struct elf_backend_data *bed,
	       asection *section,
	       bfd_vma offset,
	       elf_find_function_cache *cache)
{
  if ((sym->flags & BSF_FILE) != 0)
    {
      *file = sym;
      if (*state == symbol_seen)
	*state = file_after_symbol_seen;
      return;
    }

  if (*state == nothing_seen)
    *state = symbol_seen;

  bfd_vma code_off;
  bfd_size_type size = bed->maybe_function_sym (sym, section, &code_off);

  if (size == 0)
    return;

  if (better_fit (cache, sym, code_off, size, offset))
    {
      update_cache_with_better_match(cache, sym, code_off, size, *file, *state);
    }
  else if (should_reduce_cache_size(code_off, offset, cache))
    {
      cache->code_size = code_off - cache->code_off;
    }
}

static void
update_cache_with_better_match(elf_find_function_cache *cache,
				asymbol *sym,
				bfd_vma code_off,
				bfd_size_type size,
				asymbol *file,
				int state)
{
  cache->func = sym;
  cache->code_size = size;
  cache->code_off = code_off;
  cache->filename = NULL;

  if (file != NULL
      && ((sym->flags & BSF_LOCAL) != 0
	  || state != file_after_symbol_seen))
    cache->filename = bfd_asymbol_name (file);
}

static bfd_boolean
should_reduce_cache_size(bfd_vma code_off,
			  bfd_vma offset,
			  elf_find_function_cache *cache)
{
  return code_off > offset 
    && code_off > cache->code_off
    && code_off < cache->code_off + cache->code_size;
}
