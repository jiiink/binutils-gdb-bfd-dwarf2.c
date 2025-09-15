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
  const size_t header_size = offsetof(struct trie_leaf, ranges);
  const size_t range_item_size = sizeof(((struct trie_leaf *)0)->ranges[0]);

  if (TRIE_LEAF_SIZE > (SIZE_MAX - header_size) / range_item_size)
    return NULL;

  const size_t amt = header_size + TRIE_LEAF_SIZE * range_item_size;
  struct trie_leaf *leaf = bfd_zalloc (abfd, amt);

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
addr_range_intersects (const struct addr_range *r1,
                       const struct addr_range *r2)
{
  if (r1->start >= r1->end || r2->start >= r2->end)
    {
      return false;
    }

  return r1->start < r2->end && r2->start < r1->end;
}

/* Compare function for splay tree of addr_ranges.  */

static int
splay_tree_compare_addr_range (const void *xa, const void *xb)
{
  const struct addr_range *r1 = xa;
  const struct addr_range *r2 = xb;

  if (addr_range_intersects (r1, r2))
    {
      return 0;
    }

  if (r1->end <= r2->start)
    {
      return -1;
    }

  return 1;
}

/* Splay tree release function for keys (addr_range).  */

static void
splay_tree_free_addr_range (splay_tree_key key)
{
  /* The key is expected to be a pointer to a dynamically allocated addr_range. */
  free ((void *)key);
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
  struct info_hash_entry *new_entry = (struct info_hash_entry *) entry;

  if (new_entry == NULL)
    {
      new_entry = (struct info_hash_entry *) bfd_hash_allocate (table,
							      sizeof (*new_entry));
      if (new_entry == NULL)
	{
	  return NULL;
	}
    }

  if (bfd_hash_newfunc ((struct bfd_hash_entry *) new_entry, table, string) == NULL)
    {
      return NULL;
    }

  new_entry->head = NULL;

  return (struct bfd_hash_entry *) new_entry;
}

/* Function to create a new info hash table.  It returns a pointer to the
   newly created table or NULL if there is any error.  We need abfd
   solely for memory allocation.  */

static struct info_hash_table *
create_info_hash_table (bfd *abfd)
{
  struct info_hash_table *hash_table =
    bfd_alloc (abfd, sizeof (struct info_hash_table));

  if (hash_table == NULL)
    {
      return NULL;
    }

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
insert_info_hash_table(struct info_hash_table *hash_table,
                       const char *key,
                       void *info,
                       bool copy_p)
{
    struct info_hash_entry *entry =
        (struct info_hash_entry *)bfd_hash_lookup(&hash_table->base,
                                                  key, true, copy_p);
    if (!entry)
    {
        return false;
    }

    struct info_list_node *node =
        bfd_hash_allocate(&hash_table->base, sizeof(*node));
    if (!node)
    {
        return false;
    }

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
  if (!hash_table || !key)
    {
      return NULL;
    }

  struct info_hash_entry *entry =
    (struct info_hash_entry *) bfd_hash_lookup (&hash_table->base, key,
                                                 false, false);

  if (!entry)
    {
      return NULL;
    }

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
  const char *section_name = sec->uncompressed_name;

  if (*section_buffer == NULL)
    {
      asection *msec = bfd_get_section_by_name (abfd, section_name);
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

      bfd_size_type size = bfd_get_section_limit_octets (abfd, msec);
      bfd_size_type alloc_size = size + 1;

      if (alloc_size <= size)
	{
	  bfd_set_error (bfd_error_no_memory);
	  return false;
	}

      bfd_byte *contents = (bfd_byte *) bfd_malloc (alloc_size);
      if (contents == NULL)
	return false;

      bool success;
      if (syms)
	success = bfd_simple_get_relocated_section_contents (abfd, msec,
							     contents, syms);
      else
	success = bfd_get_section_contents (abfd, msec, contents, 0, size);

      if (!success)
	{
	  free (contents);
	  return false;
	}

      contents[size] = 0;
      *section_buffer = contents;
      *section_size = size;
    }

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

static inline bool
read_n_bytes (uint64_t *result, bfd *abfd, bfd_byte **ptr, const bfd_byte *end, size_t n)
{
  const bfd_byte *current_pos = *ptr;

  if (n == 0 || n > sizeof (*result) || (size_t) (end - current_pos) < n)
    {
      *ptr = (bfd_byte *) end;
      return false;
    }

  *result = bfd_get (n * 8, abfd, current_pos);
  *ptr = (bfd_byte *) (current_pos + n);
  return true;
}

static inline unsigned int
read_1_byte (bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 1);
}

static int
read_1_signed_byte (bfd *abfd ATTRIBUTE_UNUSED, bfd_byte **ptr, bfd_byte *end)
{
  if (!ptr || !*ptr || !end)
    {
      return 0;
    }

  if (*ptr >= end)
    {
      *ptr = end;
      return 0;
    }

  return bfd_get_signed_8 (abfd, (*ptr)++);
}

static inline unsigned int
read_2_bytes (bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 2);
}

static unsigned int
read_3_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  if ((size_t)(end - *ptr) < 3)
    {
      return 0;
    }

  const bfd_byte *p = *ptr;
  unsigned int val;

  if (bfd_little_endian (abfd))
    {
      val = (unsigned int) p[0]
          | ((unsigned int) p[1] << 8)
          | ((unsigned int) p[2] << 16);
    }
  else
    {
      val = ((unsigned int) p[0] << 16)
          | ((unsigned int) p[1] << 8)
          | (unsigned int) p[2];
    }

  *ptr += 3;
  return val;
}

static inline unsigned int
read_4_bytes (bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 4);
}

static inline uint64_t
read_8_bytes (bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 8);
}

static struct dwarf_block *
read_blk (bfd *abfd, bfd_byte **ptr, bfd_byte *end, size_t size)
{
  struct dwarf_block *block = bfd_alloc (abfd, sizeof (*block));
  if (!block)
    {
      return NULL;
    }

  ptrdiff_t available_bytes = end - *ptr;

  if (available_bytes < 0 || (size_t) available_bytes < size)
    {
      block->data = NULL;
      block->size = 0;
      *ptr = end;
    }
  else
    {
      block->data = *ptr;
      block->size = size;
      *ptr += size;
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
  bfd_byte *start = *ptr;
  bfd_byte *string_end;

  if (start >= buf_end)
    {
      return NULL;
    }

  string_end = memchr (start, '\0', buf_end - start);

  if (string_end == NULL)
    {
      *ptr = buf_end;
      return NULL;
    }

  *ptr = string_end + 1;

  if (start == string_end)
    {
      return NULL;
    }

  return (char *) start;
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
  struct dwarf2_debug_file *file = unit->file;
  uint64_t offset;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  switch (unit->offset_size)
    {
    case 4:
      offset = read_4_bytes (unit->abfd, ptr, buf_end);
      break;
    case 8:
      offset = read_8_bytes (unit->abfd, ptr, buf_end);
      break;
    default:
      *ptr = buf_end;
      return NULL;
    }

  if (!read_section (unit->abfd, &unit->stash->debug_sections[debug_str],
		     file->syms, offset,
		     &file->dwarf_str_buffer, &file->dwarf_str_size))
    {
      return NULL;
    }

  if (offset >= file->dwarf_str_size)
    {
      return NULL;
    }

  char *str = (char *) file->dwarf_str_buffer + offset;

  if (*str == '\0')
    {
      return NULL;
    }

  return str;
}

/* Like read_indirect_string but from .debug_line_str section.  */

static char *
read_indirect_line_string (struct comp_unit *unit,
			   bfd_byte **ptr,
			   bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug_file *file = unit->file;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  switch (unit->offset_size)
    {
    case 4:
      offset = read_4_bytes (unit->abfd, ptr, buf_end);
      break;
    case 8:
      offset = read_8_bytes (unit->abfd, ptr, buf_end);
      break;
    default:
      *ptr = buf_end;
      return NULL;
    }

  if (!read_section (unit->abfd,
		     &unit->stash->debug_sections[debug_line_str],
		     file->syms, offset,
		     &file->dwarf_line_str_buffer,
		     &file->dwarf_line_str_size))
    {
      return NULL;
    }

  if (offset >= file->dwarf_line_str_size)
    {
      return NULL;
    }

  char *str = (char *) file->dwarf_line_str_buffer + offset;
  if (*str == '\0')
    {
      return NULL;
    }

  return str;
}

/* Like read_indirect_string but uses a .debug_str located in
   an alternate file pointed to by the .gnu_debugaltlink section.
   Used to impement DW_FORM_GNU_strp_alt.  */

static bfd *
get_or_open_alt_bfd (struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;

  if (stash->alt.bfd_ptr)
    return stash->alt.bfd_ptr;

  char *debug_filename = bfd_follow_gnu_debugaltlink (unit->abfd, DEBUGDIR);
  if (debug_filename == NULL)
    return NULL;

  bfd *debug_bfd = bfd_openr (debug_filename, NULL);
  free (debug_filename);
  if (debug_bfd == NULL)
    return NULL;

  if (!bfd_check_format (debug_bfd, bfd_object))
    {
      bfd_close (debug_bfd);
      return NULL;
    }

  stash->alt.bfd_ptr = debug_bfd;
  return debug_bfd;
}

static char *
read_alt_indirect_string (struct comp_unit *unit,
			  bfd_byte **ptr,
			  bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash = unit->stash;
  bfd *alt_bfd;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  if (unit->offset_size == 4)
    offset = read_4_bytes (unit->abfd, ptr, buf_end);
  else
    offset = read_8_bytes (unit->abfd, ptr, buf_end);

  alt_bfd = get_or_open_alt_bfd (unit);
  if (alt_bfd == NULL)
    return NULL;

  if (! read_section (alt_bfd,
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

/* Resolve an alternate reference from UNIT at OFFSET.
   Returns a pointer into the loaded alternate CU upon success
   or NULL upon failure.  */

static bfd_byte *
read_alt_indirect_ref (struct comp_unit *unit, uint64_t offset)
{
  struct dwarf2_debug *stash = unit->stash;

  if (stash->alt.bfd_ptr == NULL)
    {
      char *debug_filename = bfd_follow_gnu_debugaltlink (unit->abfd, DEBUGDIR);
      if (debug_filename == NULL)
        return NULL;

      bfd *debug_bfd = bfd_openr (debug_filename, NULL);
      free (debug_filename);
      if (debug_bfd == NULL)
        return NULL;

      if (!bfd_check_format (debug_bfd, bfd_object))
        {
          bfd_close (debug_bfd);
          return NULL;
        }
      stash->alt.bfd_ptr = debug_bfd;
    }

  if (!read_section (stash->alt.bfd_ptr,
		     stash->debug_sections + debug_info_alt,
		     stash->alt.syms, offset,
		     &stash->alt.dwarf_info_buffer,
		     &stash->alt.dwarf_info_size))
    return NULL;

  return stash->alt.dwarf_info_buffer + offset;
}

static uint64_t
read_address (struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
  if (unit->addr_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return 0;
    }

  int signed_vma = 0;
  if (bfd_get_flavour (unit->abfd) == bfd_target_elf_flavour)
    {
      signed_vma = get_elf_backend_data (unit->abfd)->sign_extend_vma;
    }

  uint64_t address;
  bfd_byte * const buf = *ptr;

  switch (unit->addr_size)
    {
    case 8:
      address = signed_vma
	? bfd_get_signed_64 (unit->abfd, buf)
	: bfd_get_64 (unit->abfd, buf);
      break;
    case 4:
      address = signed_vma
	? bfd_get_signed_32 (unit->abfd, buf)
	: bfd_get_32 (unit->abfd, buf);
      break;
    case 2:
      address = signed_vma
	? bfd_get_signed_16 (unit->abfd, buf)
	: bfd_get_16 (unit->abfd, buf);
      break;
    default:
      abort ();
    }

  *ptr += unit->addr_size;
  return address;
}

/* Lookup an abbrev_info structure in the abbrev hash table.  */

static struct abbrev_info *
lookup_abbrev (unsigned int number, struct abbrev_info **abbrevs)
{
  if (!abbrevs)
    {
      return NULL;
    }

  const unsigned int hash_index = number % ABBREV_HASH_SIZE;

  for (struct abbrev_info *abbrev = abbrevs[hash_index]; abbrev; abbrev = abbrev->next)
    {
      if (abbrev->number == number)
	{
	  return abbrev;
	}
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
    {
      return 0;
    }

  const struct abbrev_offset_entry *ent = (const struct abbrev_offset_entry *) p;
  return htab_hash_pointer ((const void *) (uintptr_t) ent->offset);
}

static int
eq_abbrev (const void *pa, const void *pb)
{
  if (pa == NULL || pb == NULL)
    {
      return pa == pb;
    }

  const struct abbrev_offset_entry *a = (const struct abbrev_offset_entry *) pa;
  const struct abbrev_offset_entry *b = (const struct abbrev_offset_entry *) pb;

  return a->offset == b->offset;
}

static void
del_abbrev (void *p)
{
  if (!p)
    {
      return;
    }

  struct abbrev_offset_entry *ent = p;
  struct abbrev_info **abbrevs = ent->abbrevs;

  if (abbrevs)
    {
      for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
        {
          struct abbrev_info *abbrev = abbrevs[i];
          while (abbrev)
            {
              struct abbrev_info *next = abbrev->next;
              free (abbrev->attrs);
              free (abbrev);
              abbrev = next;
            }
        }
      free (abbrevs);
    }

  free (ent);
}

/* In DWARF version 2, the description of the debugging information is
   stored in a separate .debug_abbrev section.  Before we read any
   dies from a section we read in all abbreviations and install them
   in a hash table.  */

static void
free_abbrevs_table (bfd *abfd, struct abbrev_info **abbrevs)
{
  if (!abbrevs)
    return;

  for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
    {
      struct abbrev_info *abbrev = abbrevs[i];
      while (abbrev)
	{
	  struct abbrev_info *next = abbrev->next;
	  bfd_free (abbrev->attrs);
	  bfd_free (abbrev);
	  abbrev = next;
	}
    }
  bfd_free (abbrevs);
}

static bool
read_abbrev_attributes (bfd *abfd, struct abbrev_info *cur_abbrev,
			bfd_byte **abbrev_ptr_p, bfd_byte *abbrev_end)
{
  for (;;)
    {
      unsigned int abbrev_name = _bfd_safe_read_leb128 (abfd, abbrev_ptr_p,
						       false, abbrev_end);
      unsigned int abbrev_form = _bfd_safe_read_leb128 (abfd, abbrev_ptr_p,
						       false, abbrev_end);
      if (abbrev_name == 0)
	return true;

      bfd_vma implicit_const = 0;
      if (abbrev_form == DW_FORM_implicit_const)
	implicit_const = _bfd_safe_read_leb128 (abfd, abbrev_ptr_p,
						true, abbrev_end);

      if ((cur_abbrev->num_attrs % ATTR_ALLOC_CHUNK) == 0)
	{
	  size_t new_size = (cur_abbrev->num_attrs + ATTR_ALLOC_CHUNK)
	    * sizeof (struct attr_abbrev);
	  struct attr_abbrev *new_attrs = bfd_realloc (cur_abbrev->attrs,
						       new_size);
	  if (new_attrs == NULL)
	    return false;
	  cur_abbrev->attrs = new_attrs;
	}

      struct attr_abbrev *attr = &cur_abbrev->attrs[cur_abbrev->num_attrs];
      attr->name = (enum dwarf_attribute) abbrev_name;
      attr->form = (enum dwarf_form) abbrev_form;
      attr->implicit_const = implicit_const;
      cur_abbrev->num_attrs++;
    }
}

static struct abbrev_info**
read_abbrevs (bfd *abfd, uint64_t offset, struct dwarf2_debug *stash,
	      struct dwarf2_debug_file *file)
{
  struct abbrev_offset_entry ent = { offset, NULL };
  void **slot = htab_find_slot (file->abbrev_offsets, &ent, INSERT);
  if (slot == NULL)
    return NULL;
  if (*slot != NULL)
    return ((struct abbrev_offset_entry *) (*slot))->abbrevs;

  if (!read_section (abfd, &stash->debug_sections[debug_abbrev],
		     file->syms, offset,
		     &file->dwarf_abbrev_buffer,
		     &file->dwarf_abbrev_size))
    return NULL;

  size_t abbrevs_size = sizeof (struct abbrev_info *) * ABBREV_HASH_SIZE;
  struct abbrev_info **abbrevs = bfd_zalloc (abfd, abbrevs_size);
  if (abbrevs == NULL)
    return NULL;

  bfd_byte *abbrev_ptr = file->dwarf_abbrev_buffer + offset;
  bfd_byte *abbrev_end = file->dwarf_abbrev_buffer + file->dwarf_abbrev_size;
  unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr,
						     false, abbrev_end);

  while (abbrev_number)
    {
      struct abbrev_info *cur_abbrev = bfd_zalloc (abfd, sizeof (*cur_abbrev));
      if (cur_abbrev == NULL)
	{
	  free_abbrevs_table (abfd, abbrevs);
	  return NULL;
	}

      cur_abbrev->number = abbrev_number;
      cur_abbrev->tag = (enum dwarf_tag)
	_bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
      cur_abbrev->has_children = read_1_byte (abfd, &abbrev_ptr, abbrev_end);

      if (!read_abbrev_attributes (abfd, cur_abbrev, &abbrev_ptr, abbrev_end))
	{
	  bfd_free (cur_abbrev->attrs);
	  bfd_free (cur_abbrev);
	  free_abbrevs_table (abfd, abbrevs);
	  return NULL;
	}

      unsigned int hash_number = abbrev_number % ABBREV_HASH_SIZE;
      cur_abbrev->next = abbrevs[hash_number];
      abbrevs[hash_number] = cur_abbrev;

      if ((size_t) (abbrev_ptr - file->dwarf_abbrev_buffer)
	  >= file->dwarf_abbrev_size)
	break;

      abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr,
					     false, abbrev_end);
      if (abbrev_number != 0 && lookup_abbrev (abbrev_number, abbrevs) != NULL)
	break;
    }

  struct abbrev_offset_entry *new_ent = bfd_malloc (sizeof (*new_ent));
  if (new_ent == NULL)
    {
      free_abbrevs_table (abfd, abbrevs);
      return NULL;
    }

  new_ent->offset = offset;
  new_ent->abbrevs = abbrevs;
  *slot = new_ent;

  return abbrevs;
}

/* Returns true if the form is one which has a string value.  */

static bool
is_str_form (const struct attribute *attr)
{
  if (!attr)
    {
      return false;
    }

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
  static const unsigned int int_forms[] = {
    DW_FORM_addr,
    DW_FORM_addrx,
    DW_FORM_addrx1,
    DW_FORM_addrx2,
    DW_FORM_addrx3,
    DW_FORM_addrx4,
    DW_FORM_data1,
    DW_FORM_data2,
    DW_FORM_data4,
    DW_FORM_data8,
    DW_FORM_flag,
    DW_FORM_flag_present,
    DW_FORM_GNU_ref_alt,
    DW_FORM_implicit_const,
    DW_FORM_ref1,
    DW_FORM_ref2,
    DW_FORM_ref4,
    DW_FORM_ref8,
    DW_FORM_ref_addr,
    DW_FORM_ref_sig8,
    DW_FORM_ref_udata,
    DW_FORM_sdata,
    DW_FORM_sec_offset,
    DW_FORM_udata
  };
  const unsigned int form_to_check = attr->form;

  for (size_t i = 0; i < sizeof (int_forms) / sizeof (int_forms[0]); ++i)
    {
      if (int_forms[i] == form_to_check)
        {
          return true;
        }
    }

  return false;
}

/* Returns true if the form is strx[1-4].  */

static inline bool
is_strx_form (enum dwarf_form form)
{
  switch (form)
    {
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
  if (unit == NULL || unit->stash == NULL || unit->file == NULL)
    return 0;

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_addr],
		     file->syms, 0,
		     &file->dwarf_addr_buffer, &file->dwarf_addr_size))
    return 0;

  size_t offset;
  if (_bfd_mul_overflow (idx, unit->addr_size, &offset))
    return 0;

  offset += unit->dwarf_addr_offset;
  if (offset < unit->dwarf_addr_offset)
    return 0;

  if (unit->addr_size > file->dwarf_addr_size
      || offset > file->dwarf_addr_size - unit->addr_size)
    return 0;

  bfd_byte *info_ptr = file->dwarf_addr_buffer + offset;

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
  if (unit == NULL || unit->stash == NULL || unit->file == NULL)
    return NULL;

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_str],
		     file->syms, 0,
		     &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_str_offsets],
		     file->syms, 0,
		     &file->dwarf_str_offsets_buffer,
		     &file->dwarf_str_offsets_size))
    return NULL;

  size_t offset;
  if (_bfd_mul_overflow (idx, unit->offset_size, &offset))
    return NULL;

  if (offset > SIZE_MAX - unit->dwarf_str_offset)
    return NULL;
  offset += unit->dwarf_str_offset;

  if (unit->offset_size > file->dwarf_str_offsets_size
      || offset > file->dwarf_str_offsets_size - unit->offset_size)
    return NULL;

  const bfd_byte *info_ptr = file->dwarf_str_offsets_buffer + offset;

  uint64_t str_offset;
  switch (unit->offset_size)
    {
    case 4:
      str_offset = bfd_get_32 (unit->abfd, info_ptr);
      break;
    case 8:
      str_offset = bfd_get_64 (unit->abfd, info_ptr);
      break;
    default:
      return NULL;
    }

  if (str_offset >= file->dwarf_str_size)
    return NULL;

  return (const char *) file->dwarf_str_buffer + str_offset;
}

/* Read and fill in the value of attribute ATTR as described by FORM.
   Read data starting from INFO_PTR, but never at or beyond INFO_PTR_END.
   Returns an updated INFO_PTR taking into account the amount of data read.  */

static bfd_vma
read_offset (struct comp_unit *unit, bfd_byte **info_ptr_p,
	     bfd_byte *info_ptr_end)
{
  if (unit->offset_size == 4)
    return read_4_bytes (unit->abfd, info_ptr_p, info_ptr_end);
  return read_8_bytes (unit->abfd, info_ptr_p, info_ptr_end);
}

static bool
process_block_form (struct attribute *attr, size_t amt, bfd *abfd,
		    bfd_byte **info_ptr_p, bfd_byte *info_ptr_end)
{
  attr->u.blk = read_blk (abfd, info_ptr_p, info_ptr_end, amt);
  return attr->u.blk != NULL;
}

static void
process_addrx_form (struct attribute *attr, bfd_vma index,
		    const struct comp_unit *unit)
{
  attr->u.val = index;
  if (unit->dwarf_addr_offset != 0)
    attr->u.val = read_indexed_address (index, unit);
}

static void
process_strx_form (struct attribute *attr, bfd_vma index,
		   const struct comp_unit *unit)
{
  attr->u.val = index;
  attr->u.str = NULL;
  if (unit->dwarf_str_offset != 0)
    attr->u.str = (char *) read_indexed_string (index, unit);
}

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

    case DW_FORM_addr:
      attr->u.val = read_address (unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_ref_addr:
      if (unit->version < 3)
	attr->u.val = read_address (unit, &info_ptr, info_ptr_end);
      else
	attr->u.val = read_offset (unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_GNU_ref_alt:
    case DW_FORM_sec_offset:
      attr->u.val = read_offset (unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_exprloc:
    case DW_FORM_block:
      amt = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      if (!process_block_form (attr, amt, abfd, &info_ptr, info_ptr_end))
	return NULL;
      break;

    case DW_FORM_block1:
      amt = read_1_byte (abfd, &info_ptr, info_ptr_end);
      if (!process_block_form (attr, amt, abfd, &info_ptr, info_ptr_end))
	return NULL;
      break;

    case DW_FORM_block2:
      amt = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      if (!process_block_form (attr, amt, abfd, &info_ptr, info_ptr_end))
	return NULL;
      break;

    case DW_FORM_block4:
      amt = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      if (!process_block_form (attr, amt, abfd, &info_ptr, info_ptr_end))
	return NULL;
      break;

    case DW_FORM_data16:
      if (!process_block_form (attr, 16, abfd, &info_ptr, info_ptr_end))
	return NULL;
      break;

    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_data2:
    case DW_FORM_ref2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_ref4:
    case DW_FORM_data4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_data8:
    case DW_FORM_ref8:
    case DW_FORM_ref_sig8:
      attr->u.val = read_8_bytes (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_sdata:
      attr->u.sval = _bfd_safe_read_leb128 (abfd, &info_ptr, true, info_ptr_end);
      break;

    case DW_FORM_rnglistx:
    case DW_FORM_loclistx:
    case DW_FORM_udata:
    case DW_FORM_ref_udata:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
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

    case DW_FORM_addrx:
      process_addrx_form (attr, _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end), unit);
      break;

    case DW_FORM_addrx1:
      process_addrx_form (attr, read_1_byte (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_addrx2:
      process_addrx_form (attr, read_2_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_addrx3:
      process_addrx_form (attr, read_3_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_addrx4:
      process_addrx_form (attr, read_4_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_strx:
      process_strx_form (attr, _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end), unit);
      break;

    case DW_FORM_strx1:
      process_strx_form (attr, read_1_byte (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_strx2:
      process_strx_form (attr, read_2_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_strx3:
      process_strx_form (attr, read_3_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_strx4:
      process_strx_form (attr, read_4_bytes (abfd, &info_ptr, info_ptr_end), unit);
      break;

    case DW_FORM_indirect:
      form = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      if (form == DW_FORM_implicit_const)
	implicit_const = _bfd_safe_read_leb128 (abfd, &info_ptr, true, info_ptr_end);
      info_ptr = read_attribute_value (attr, form, implicit_const, unit,
				       info_ptr, info_ptr_end);
      break;

    case DW_FORM_implicit_const:
      attr->form = DW_FORM_sdata;
      attr->u.sval = implicit_const;
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
read_attribute (struct attribute *attr,
                const struct attr_abbrev *abbrev,
                struct comp_unit *unit,
                bfd_byte *info_ptr,
                const bfd_byte *info_ptr_end)
{
  if (!attr || !abbrev)
    {
      return NULL;
    }

  attr->name = abbrev->name;

  return read_attribute_value (attr, abbrev->form, abbrev->implicit_const,
			       unit, info_ptr, info_ptr_end);
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
    case DW_LANG_C99:
    case DW_LANG_C11:
    case DW_LANG_C17:
    case DW_LANG_C23:
    case DW_LANG_UPC:
    case DW_LANG_Upc:
    case DW_LANG_Cobol74:
    case DW_LANG_Cobol85:
    case DW_LANG_Fortran77:
    case DW_LANG_Fortran18:
    case DW_LANG_Fortran23:
    case DW_LANG_Pascal83:
    case DW_LANG_PLI:
    case DW_LANG_Mips_Assembler:
    case DW_LANG_Assembly:
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
new_line_sorts_after (const struct line_info *new_line,
		      const struct line_info *line)
{
  if (new_line->address != line->address)
    {
      return new_line->address > line->address;
    }
  return new_line->op_index > line->op_index;
}


/* Adds a new entry to the line_info list in the line_info_table, ensuring
   that the list is sorted.  Note that the line_info list is sorted from
   highest to lowest VMA (with possible duplicates); that is,
   line_info->prev_line always accesses an equal or smaller VMA.  */

static struct line_info *
create_line_info_node (struct line_info_table *table,
		       bfd_vma address,
		       unsigned char op_index,
		       const char *filename,
		       unsigned int line,
		       unsigned int column,
		       unsigned int discriminator,
		       int end_sequence)
{
  struct line_info *info = (struct line_info *) bfd_alloc (table->abfd, sizeof (struct line_info));
  if (info == NULL)
    return NULL;

  info->prev_line = NULL;
  info->address = address;
  info->op_index = op_index;
  info->line = line;
  info->column = column;
  info->discriminator = discriminator;
  info->end_sequence = end_sequence;

  if (filename != NULL && *filename != '\0')
    {
      size_t len = strlen (filename);
      info->filename = (char *) bfd_alloc (table->abfd, len + 1);
      if (info->filename == NULL)
	{
	  return NULL;
	}
      memcpy (info->filename, filename, len + 1);
    }
  else
    {
      info->filename = NULL;
    }

  return info;
}

static bool
start_new_line_sequence (struct line_info_table *table, struct line_info *info)
{
  struct line_sequence *seq = (struct line_sequence *) bfd_malloc (sizeof (struct line_sequence));
  if (seq == NULL)
    return false;

  seq->low_pc = info->address;
  seq->prev_sequence = table->sequences;
  seq->last_line = info;
  table->sequences = seq;
  table->lcl_head = info;
  table->num_sequences++;
  return true;
}

static void
find_and_insert_in_sequence (struct line_info_table *table, struct line_info *info)
{
  struct line_sequence *seq = table->sequences;
  struct line_info *li2 = seq->last_line;
  struct line_info *li1 = li2->prev_line;

  while (li1 != NULL)
    {
      if (!new_line_sorts_after (info, li2)
	  && new_line_sorts_after (info, li1))
	break;

      li2 = li1;
      li1 = li1->prev_line;
    }

  table->lcl_head = li2;
  info->prev_line = li2->prev_line;
  li2->prev_line = info;

  if (info->address < seq->low_pc)
    seq->low_pc = info->address;
}

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
  struct line_info *info = create_line_info_node (table, address, op_index,
						  filename, line, column,
						  discriminator, end_sequence);
  if (info == NULL)
    return false;

  struct line_sequence *seq = table->sequences;

  if (seq == NULL || seq->last_line->end_sequence)
    {
      if (!start_new_line_sequence (table, info))
	{
	  return false;
	}
      return true;
    }

  if (seq->last_line->address == address
      && seq->last_line->op_index == op_index
      && seq->last_line->end_sequence == end_sequence)
    {
      if (table->lcl_head == seq->last_line)
	table->lcl_head = info;
      info->prev_line = seq->last_line->prev_line;
      seq->last_line = info;
      return true;
    }

  if (info->end_sequence || new_line_sorts_after (info, seq->last_line))
    {
      info->prev_line = seq->last_line;
      seq->last_line = info;
      if (table->lcl_head == NULL)
	table->lcl_head = info;
      return true;
    }

  if (!new_line_sorts_after (info, table->lcl_head)
      && (table->lcl_head->prev_line == NULL
	  || new_line_sorts_after (info, table->lcl_head->prev_line)))
    {
      info->prev_line = table->lcl_head->prev_line;
      table->lcl_head->prev_line = info;
      return true;
    }

  find_and_insert_in_sequence (table, info);
  return true;
}

/* Extract a fully qualified filename from a line info table.
   The returned string has been malloc'ed and it is the caller's
   responsibility to free it.  */

static char *
concat_filename (struct line_info_table *table, unsigned int file)
{
  /* Pre DWARF-5 entry 0 in the directory and filename tables was not used.
     So in order to save space in the tables used here the info for, eg
     directory 1 is stored in slot 0 of the directory table, directory 2
     in slot 1 and so on.

     Starting with DWARF-5 the 0'th entry is used so there is a one to one
     mapping between DWARF slots and internal table entries.  */

  if (table == NULL)
    return strdup ("<unknown>");

  if (!table->use_dir_and_file_0)
    {
      if (file == 0)
	return strdup ("<unknown>");
      --file;
    }

  if (file >= table->num_files)
    {
      _bfd_error_handler
	(_("DWARF error: mangled line number section (bad file number)"));
      return strdup ("<unknown>");
    }

  const char *filename = table->files[file].name;
  if (filename == NULL)
    return strdup ("<unknown>");

  if (IS_ABSOLUTE_PATH (filename))
    return strdup (filename);

  unsigned int dir_idx = table->files[file].dir;
  if (!table->use_dir_and_file_0)
    --dir_idx;

  const char *sub_dir = (dir_idx < table->num_dirs) ? table->dirs[dir_idx] : NULL;
  const char *comp_dir = table->comp_dir;

  const char *base_dir = NULL;
  const char *mid_dir = NULL;

  if (sub_dir && IS_ABSOLUTE_PATH (sub_dir))
    {
      base_dir = sub_dir;
    }
  else
    {
      base_dir = comp_dir;
      mid_dir = sub_dir;
    }

  if (!base_dir)
    {
      base_dir = mid_dir;
      mid_dir = NULL;
    }

  if (!base_dir)
    return strdup (filename);

  size_t base_len = strlen (base_dir);
  size_t file_len = strlen (filename);
  size_t mid_len = mid_dir ? strlen (mid_dir) : 0;
  size_t total_len;
  char *full_path;

  if (mid_dir)
    total_len = base_len + 1 + mid_len + 1 + file_len + 1;
  else
    total_len = base_len + 1 + file_len + 1;

  full_path = (char *) bfd_malloc (total_len);
  if (full_path == NULL)
    return NULL;

  if (mid_dir)
    snprintf (full_path, total_len, "%s/%s/%s", base_dir, mid_dir, filename);
  else
    snprintf (full_path, total_len, "%s/%s", base_dir, filename);

  return full_path;
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
  return low1 <= high2 && low2 <= high1;
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

      if (leaf->num_stored_in_leaf < trie->num_room_in_leaf)
	{
	  unsigned int i = leaf->num_stored_in_leaf++;
	  leaf->ranges[i].unit = unit;
	  leaf->ranges[i].low_pc = low_pc;
	  leaf->ranges[i].high_pc = high_pc;
	  return trie;
	}

      bool splitting_helps = false;
      if (trie_pc_bits < VMA_BITS)
	{
	  bfd_vma bucket_high_pc = trie_pc + ((bfd_vma) -1 >> trie_pc_bits);
	  for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
	    {
	      if (leaf->ranges[i].low_pc > trie_pc
		  || leaf->ranges[i].high_pc <= bucket_high_pc)
		{
		  splitting_helps = true;
		  break;
		}
	    }
	}

      if (splitting_helps)
	{
	  const struct trie_leaf *old_leaf = (const struct trie_leaf *) trie;
	  struct trie_node *new_trie = bfd_zalloc (abfd, sizeof (struct trie_interior));
	  if (!new_trie)
	    return NULL;

	  for (unsigned int i = 0; i < old_leaf->num_stored_in_leaf; ++i)
	    {
	      struct trie_node *result =
		insert_arange_in_trie (abfd, new_trie, trie_pc, trie_pc_bits,
				       old_leaf->ranges[i].unit,
				       old_leaf->ranges[i].low_pc,
				       old_leaf->ranges[i].high_pc);
	      if (!result)
		return NULL;
	      new_trie = result;
	    }
	  trie = new_trie;
	}
      else
	{
	  const struct trie_leaf *old_leaf = (const struct trie_leaf *) trie;
	  unsigned int new_room = trie->num_room_in_leaf * 2;
	  size_t amt = sizeof (*leaf) + new_room * sizeof (leaf->ranges[0]);
	  struct trie_leaf *new_leaf = bfd_zalloc (abfd, amt);

	  if (!new_leaf)
	    return NULL;

	  new_leaf->head.num_room_in_leaf = new_room;
	  new_leaf->num_stored_in_leaf = old_leaf->num_stored_in_leaf;
	  memcpy (new_leaf->ranges, old_leaf->ranges,
		  old_leaf->num_stored_in_leaf * sizeof (old_leaf->ranges[0]));

	  unsigned int i = new_leaf->num_stored_in_leaf++;
	  new_leaf->ranges[i].unit = unit;
	  new_leaf->ranges[i].low_pc = low_pc;
	  new_leaf->ranges[i].high_pc = high_pc;
	  return &new_leaf->head;
	}
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

  if (clamped_low_pc >= clamped_high_pc)
    return trie;

  unsigned int shift = VMA_BITS - trie_pc_bits - 8;
  int from_ch = (clamped_low_pc >> shift) & 0xff;
  int to_ch = ((clamped_high_pc - 1) >> shift) & 0xff;
  struct trie_interior *interior = (struct trie_interior *) trie;

  for (int ch = from_ch; ch <= to_ch; ++ch)
    {
      struct trie_node *child = interior->children[ch];
      if (!child)
	{
	  child = alloc_trie_leaf (abfd);
	  if (!child)
	    return NULL;
	}

      bfd_vma bucket = (bfd_vma) ch << shift;
      struct trie_node *new_child =
	insert_arange_in_trie (abfd, child, trie_pc + bucket,
			       trie_pc_bits + 8, unit, low_pc, high_pc);
      if (!new_child)
	return NULL;

      interior->children[ch] = new_child;
    }

  return trie;
}

static bool
arange_add (struct comp_unit *unit, struct arange *first_arange,
	    struct trie_node **trie_root, bfd_vma low_pc, bfd_vma high_pc)
{
  if (low_pc == high_pc)
    {
      return true;
    }

  if (trie_root)
    {
      *trie_root = insert_arange_in_trie (unit->file->bfd_ptr,
					  *trie_root,
					  0,
					  0,
					  unit,
					  low_pc,
					  high_pc);
      if (!*trie_root)
	{
	  return false;
	}
    }

  if (first_arange->high == 0)
    {
      first_arange->low = low_pc;
      first_arange->high = high_pc;
      return true;
    }

  for (struct arange *current = first_arange; current; current = current->next)
    {
      if (low_pc == current->high)
	{
	  current->high = high_pc;
	  return true;
	}
      if (high_pc == current->low)
	{
	  current->low = low_pc;
	  return true;
	}
    }

  struct arange *new_arange = bfd_alloc (unit->abfd, sizeof (*new_arange));
  if (!new_arange)
    {
      return false;
    }

  new_arange->low = low_pc;
  new_arange->high = high_pc;
  new_arange->next = first_arange->next;
  first_arange->next = new_arange;

  return true;
}

/* Compare function for line sequences.  */

static int
compare_sequences (const void* a, const void* b)
{
  const struct line_sequence* seq1 = a;
  const struct line_sequence* seq2 = b;

  if (seq1->low_pc < seq2->low_pc)
    return -1;
  if (seq1->low_pc > seq2->low_pc)
    return 1;

  if (seq2->last_line->address < seq1->last_line->address)
    return -1;
  if (seq2->last_line->address > seq1->last_line->address)
    return 1;

  if (seq2->last_line->op_index < seq1->last_line->op_index)
    return -1;
  if (seq2->last_line->op_index > seq1->last_line->op_index)
    return 1;

  if (seq1->num_lines < seq2->num_lines)
    return -1;
  if (seq1->num_lines > seq2->num_lines)
    return 1;

  return 0;
}

/* Construct the line information table for quick lookup.  */

static bool
build_line_info_table (struct line_info_table *table,
		       struct line_sequence *seq)
{
  struct line_info **line_info_lookup;
  struct line_info *each_line;
  unsigned int num_lines;
  unsigned int line_index;

  if (seq->line_info_lookup != NULL)
    {
      return true;
    }

  num_lines = 0;
  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    {
      num_lines++;
    }

  seq->num_lines = num_lines;
  if (num_lines == 0)
    {
      return true;
    }

  if (num_lines > ((size_t) -1) / sizeof (struct line_info *))
    {
      return false;
    }

  line_info_lookup = bfd_alloc (table->abfd,
				sizeof (struct line_info *) * num_lines);
  if (line_info_lookup == NULL)
    {
      return false;
    }
  seq->line_info_lookup = line_info_lookup;

  line_index = num_lines;
  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    {
      line_info_lookup[--line_index] = each_line;
    }

  BFD_ASSERT (line_index == 0);
  return true;
}

/* Sort the line sequences for quick lookup.  */

static bool
sort_line_sequences (struct line_info_table* table)
{
  const unsigned int count = table->num_sequences;
  if (count == 0)
    return true;

  size_t element_size = sizeof (struct line_sequence);
  if (element_size > 0 && count > (size_t)-1 / element_size)
    return false;

  size_t amt = element_size * count;
  struct line_sequence *sequences = (struct line_sequence *) bfd_alloc (table->abfd, amt);
  if (sequences == NULL)
    return false;

  struct line_sequence *node = table->sequences;
  for (unsigned int i = 0; i < count; ++i)
    {
      BFD_ASSERT (node != NULL);
      struct line_sequence *next_node = node->prev_sequence;

      sequences[i].low_pc = node->low_pc;
      sequences[i].last_line = node->last_line;
      sequences[i].prev_sequence = NULL;
      sequences[i].line_info_lookup = NULL;
      sequences[i].num_lines = i;

      free (node);
      node = next_node;
    }
  BFD_ASSERT (node == NULL);

  qsort (sequences, count, sizeof (struct line_sequence), compare_sequences);

  unsigned int write_idx = 1;
  bfd_vma last_high_pc = sequences[0].last_line->address;

  for (unsigned int read_idx = 1; read_idx < count; ++read_idx)
    {
      struct line_sequence *current_seq = &sequences[read_idx];

      if (current_seq->low_pc < last_high_pc
          && current_seq->last_line->address <= last_high_pc)
        {
          continue;
        }

      if (current_seq->low_pc < last_high_pc)
        {
          current_seq->low_pc = last_high_pc;
        }

      last_high_pc = current_seq->last_line->address;

      if (write_idx < read_idx)
        {
          sequences[write_idx] = *current_seq;
        }
      write_idx++;
    }

  table->sequences = sequences;
  table->num_sequences = write_idx;
  return true;
}

/* Add directory to TABLE.  CUR_DIR memory ownership is taken by TABLE.  */

static bool
line_info_add_include_dir (struct line_info_table *table, char *cur_dir)
{
  if ((table->num_dirs % DIR_ALLOC_CHUNK) == 0)
    {
      size_t new_capacity = table->num_dirs + DIR_ALLOC_CHUNK;

      if (new_capacity < table->num_dirs || new_capacity > SIZE_MAX / sizeof (*table->dirs))
	{
	  return false;
	}

      size_t new_size = new_capacity * sizeof (*table->dirs);
      char **new_dirs = bfd_realloc (table->dirs, new_size);

      if (new_dirs == NULL)
	{
	  return false;
	}
      table->dirs = new_dirs;
    }

  table->dirs[table->num_dirs++] = cur_dir;
  return true;
}

static bool
line_info_add_include_dir_stub (struct line_info_table *table, char *cur_dir,
                                unsigned int,
                                unsigned int,
                                unsigned int)
{
  return line_info_add_include_dir (table, cur_dir);
}

/* Add file to TABLE.  CUR_FILE memory ownership is taken by TABLE.  */

static bool
line_info_add_file_name (struct line_info_table *table, char *cur_file,
			 unsigned int dir, unsigned int xtime,
			 unsigned int size)
{
  if ((table->num_files % FILE_ALLOC_CHUNK) == 0)
    {
      size_t new_count = (size_t) table->num_files + FILE_ALLOC_CHUNK;
      size_t new_size;
      struct fileinfo *new_files;

      if (new_count > SIZE_MAX / sizeof (struct fileinfo))
	{
	  return false;
	}

      new_size = new_count * sizeof (struct fileinfo);
      new_files = bfd_realloc (table->files, new_size);

      if (new_files == NULL)
	{
	  return false;
	}
      table->files = new_files;
    }

  struct fileinfo *new_entry = &table->files[table->num_files];
  new_entry->name = cur_file;
  new_entry->dir = dir;
  new_entry->time = xtime;
  new_entry->size = size;

  table->num_files++;
  return true;
}

/* Read directory or file name entry format, starting with byte of
   format count entries, ULEB128 pairs of entry formats, ULEB128 of
   entries count and the entries themselves in the described entry
   format.  */

static bfd_byte *
read_one_data_entry (struct fileinfo *fe,
		     struct comp_unit *unit,
		     bfd_byte *format_header_data,
		     bfd_byte format_count,
		     bfd_byte *buf,
		     bfd_byte *buf_end)
{
  bfd *abfd = unit->abfd;
  bfd_byte *format = format_header_data;

  memset (fe, 0, sizeof (*fe));

  for (bfd_byte formati = 0; formati < format_count; formati++)
    {
      bfd_vma content_type, form;
      struct attribute attr;
      char **stringp = NULL;
      unsigned int *uintp = NULL;

      content_type = _bfd_safe_read_leb128 (abfd, &format, false, buf_end);
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
	  return NULL;
	}

      form = _bfd_safe_read_leb128 (abfd, &format, false, buf_end);
      buf = read_attribute_value (&attr, form, 0, unit, buf, buf_end);
      if (buf == NULL)
	return NULL;

      switch (form)
	{
	case DW_FORM_string:
	case DW_FORM_line_strp:
	case DW_FORM_strx:
	case DW_FORM_strx1:
	case DW_FORM_strx2:
	case DW_FORM_strx3:
	case DW_FORM_strx4:
	  if (stringp)
	    *stringp = attr.u.str;
	  break;
	case DW_FORM_data1:
	case DW_FORM_data2:
	case DW_FORM_data4:
	case DW_FORM_data8:
	case DW_FORM_udata:
	  if (uintp)
	    *uintp = attr.u.val;
	  break;
	case DW_FORM_data16:
	  /* MD5 data is in the attr.blk, but we are ignoring those.  */
	  break;
	}
    }
  return buf;
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
  bfd_byte *buf = *bufp;
  bfd_byte format_count;
  bfd_byte *format_header_data;
  bfd_vma data_count;
  bfd_vma datai;

  format_count = read_1_byte (abfd, &buf, buf_end);
  format_header_data = buf;
  for (bfd_byte i = 0; i < format_count; i++)
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

  /* PR 22210.  Paranoia check.  Don't bother running the loop
     if we know that we are going to run out of buffer.  */
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
      struct fileinfo fe;
      bfd_byte *next_buf = read_one_data_entry (&fe, unit, format_header_data,
					       format_count, buf, buf_end);
      if (next_buf == NULL)
	return false;
      buf = next_buf;

      if (!callback (table, fe.name, fe.dir, fe.time, fe.size))
	return false;
    }

  *bufp = buf;
  return true;
}

/* Decode the line number information for UNIT.  */

static void
free_line_info_table_contents (struct line_info_table *table)
{
  if (!table)
    return;

  while (table->sequences != NULL)
    {
      struct line_sequence *seq = table->sequences;
      table->sequences = table->sequences->prev_sequence;
      free (seq);
    }
  free (table->files);
  table->files = NULL;
  free (table->dirs);
  table->dirs = NULL;
}

static void
update_address_range (bfd_vma *low_pc, bfd_vma *high_pc, bfd_vma address)
{
  if (address < *low_pc)
    *low_pc = address;
  if (address > *high_pc)
    *high_pc = address;
}

static void
advance_address_and_op_index (bfd_vma *address, unsigned char *op_index,
			      const struct line_head *lh, bfd_vma adjustment)
{
  if (lh->maximum_ops_per_insn == 1)
    {
      *address += adjustment * lh->minimum_instruction_length;
    }
  else
    {
      bfd_vma total_ops = *op_index + adjustment;
      *address += ((total_ops / lh->maximum_ops_per_insn)
		   * lh->minimum_instruction_length);
      *op_index = (unsigned char) (total_ops % lh->maximum_ops_per_insn);
    }
}

static bool
read_line_prologue (struct comp_unit *unit, struct line_head *lh,
		    bfd_byte **line_ptr_p, bfd_byte **line_end_p)
{
  bfd *abfd = unit->abfd;
  bfd_byte *line_ptr = *line_ptr_p;
  bfd_byte *line_end = *line_end_p;
  unsigned int offset_size;
  size_t min_prologue_header_size;

  lh->total_length = read_4_bytes (abfd, &line_ptr, line_end);
  offset_size = 4;
  if (lh->total_length == 0xffffffff)
    {
      lh->total_length = read_8_bytes (abfd, &line_ptr, line_end);
      offset_size = 8;
    }
  else if (lh->total_length == 0 && unit->addr_size == 8)
    {
      lh->total_length = read_4_bytes (abfd, &line_ptr, line_end);
      offset_size = 8;
    }

  if (lh->total_length > (size_t) (line_end - line_ptr))
    {
      _bfd_error_handler
	(_("DWARF error: line info data is bigger (%#" PRIx64 ")"
	   " than the space remaining in the section (%#lx)"),
	 (uint64_t) lh->total_length, (unsigned long) (line_end - line_ptr));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  *line_end_p = line_ptr + lh->total_length;
  line_end = *line_end_p;

  lh->version = read_2_bytes (abfd, &line_ptr, line_end);
  if (lh->version < 2 || lh->version > 5)
    {
      _bfd_error_handler
	(_("DWARF error: unhandled .debug_line version %d"), lh->version);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  min_prologue_header_size = offset_size;
  min_prologue_header_size += (lh->version >= 5) ? 8 : (lh->version >= 4 ? 6 : 5);

  if ((size_t) (line_end - line_ptr) < min_prologue_header_size)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading prologue"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (lh->version >= 5)
    {
      unsigned int segment_selector_size;
      (void) read_1_byte (abfd, &line_ptr, line_end);
      segment_selector_size = read_1_byte (abfd, &line_ptr, line_end);
      if (segment_selector_size != 0)
	{
	  _bfd_error_handler
	    (_("DWARF error: line info unsupported segment selector size %u"),
	     segment_selector_size);
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
    }

  lh->prologue_length = (offset_size == 4)
    ? read_4_bytes (abfd, &line_ptr, line_end)
    : read_8_bytes (abfd, &line_ptr, line_end);

  lh->minimum_instruction_length = read_1_byte (abfd, &line_ptr, line_end);
  lh->maximum_ops_per_insn = (lh->version >= 4)
    ? read_1_byte (abfd, &line_ptr, line_end) : 1;

  if (lh->maximum_ops_per_insn == 0)
    {
      _bfd_error_handler
	(_("DWARF error: invalid maximum operations per instruction"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  lh->default_is_stmt = read_1_byte (abfd, &line_ptr, line_end);
  lh->line_base = read_1_signed_byte (abfd, &line_ptr, line_end);
  lh->line_range = read_1_byte (abfd, &line_ptr, line_end);
  lh->opcode_base = read_1_byte (abfd, &line_ptr, line_end);

  if ((size_t) (line_end - line_ptr) < (size_t) (lh->opcode_base - 1))
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading opcodes"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  lh->standard_opcode_lengths = (unsigned char *) bfd_alloc (abfd, lh->opcode_base);
  if (lh->standard_opcode_lengths == NULL)
    return false;

  lh->standard_opcode_lengths[0] = 1;
  for (unsigned int i = 1; i < lh->opcode_base; ++i)
    lh->standard_opcode_lengths[i] = read_1_byte (abfd, &line_ptr, line_end);

  *line_ptr_p = line_ptr;
  return true;
}

static bool
read_file_and_dir_tables (struct comp_unit *unit,
			  struct line_info_table *table,
			  bfd_byte **line_ptr_p, bfd_byte *line_end,
			  int version)
{
  bfd *abfd = unit->abfd;
  bfd_byte *line_ptr = *line_ptr_p;
  char *str;

  if (version >= 5)
    {
      if (!read_formatted_entries (unit, &line_ptr, line_end, table,
				   line_info_add_include_dir_stub)
	  || !read_formatted_entries (unit, &line_ptr, line_end, table,
				      line_info_add_file_name))
	return false;
      table->use_dir_and_file_0 = true;
    }
  else
    {
      while ((str = read_string (&line_ptr, line_end)) != NULL)
	{
	  if (!line_info_add_include_dir (table, str))
	    return false;
	}

      while ((str = read_string (&line_ptr, line_end)) != NULL)
	{
	  unsigned int dir = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
	  unsigned int xtime = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
	  unsigned int size = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);

	  if (!line_info_add_file_name (table, str, dir, xtime, size))
	    return false;
	}
      table->use_dir_and_file_0 = false;
    }

  *line_ptr_p = line_ptr;
  return true;
}

static bool
execute_statement_program (struct comp_unit *unit,
			   struct line_info_table *table,
			   const struct line_head *lh,
			   bfd_byte *line_ptr, bfd_byte *line_end)
{
  bfd *abfd = unit->abfd;

  while (line_ptr < line_end)
    {
      bfd_vma address = 0;
      unsigned char op_index = 0;
      unsigned int line = 1;
      unsigned int column = 0;
      unsigned int discriminator = 0;
      int is_stmt = lh->default_is_stmt;
      char *filename = NULL;
      bool end_sequence = false;
      bfd_vma low_pc = (bfd_vma) -1;
      bfd_vma high_pc = 0;

      if (table->num_files)
	filename = concat_filename (table, 1);

      while (!end_sequence && line_ptr < line_end)
	{
	  unsigned char op_code = read_1_byte (abfd, &line_ptr, line_end);

	  if (op_code >= lh->opcode_base)
	    {
	      unsigned char adj_opcode = op_code - lh->opcode_base;
	      if (lh->line_range == 0)
		goto fail_sequence;
	      advance_address_and_op_index (&address, &op_index, lh,
					    adj_opcode / lh->line_range);
	      line += lh->line_base + (adj_opcode % lh->line_range);
	      if (!add_line_info (table, address, op_index, filename, line,
				  column, discriminator, false))
		goto fail_sequence;
	      discriminator = 0;
	      update_address_range (&low_pc, &high_pc, address);
	    }
	  else
	    {
	      switch (op_code)
		{
		case DW_LNS_extended_op:
		  {
		    unsigned int exop_len = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
		    bfd_byte *op_end = line_ptr + exop_len;
		    unsigned char extended_op = read_1_byte (abfd, &line_ptr, op_end);

		    switch (extended_op)
		      {
		      case DW_LNE_end_sequence:
			end_sequence = true;
			if (!add_line_info (table, address, op_index, filename, line,
					    column, discriminator, true))
			  goto fail_sequence;
			discriminator = 0;
			update_address_range (&low_pc, &high_pc, address);
			if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
					 low_pc, high_pc))
			  goto fail_sequence;
			break;
		      case DW_LNE_set_address:
			address = read_address (unit, &line_ptr, op_end);
			op_index = 0;
			break;
		      case DW_LNE_define_file:
			{
			  char *cur_file = read_string (&line_ptr, op_end);
			  unsigned int dir = _bfd_safe_read_leb128 (abfd, &line_ptr, false, op_end);
			  unsigned int xtime = _bfd_safe_read_leb128 (abfd, &line_ptr, false, op_end);
			  unsigned int size = _bfd_safe_read_leb128 (abfd, &line_ptr, false, op_end);
			  if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
			    goto fail_sequence;
			}
			break;
		      case DW_LNE_set_discriminator:
			discriminator = _bfd_safe_read_leb128 (abfd, &line_ptr, false, op_end);
			break;
		      case DW_LNE_HP_source_file_correlation:
			line_ptr = op_end;
			break;
		      default:
			goto fail_sequence;
		      }
		  }
		  break;
		case DW_LNS_copy:
		  if (!add_line_info (table, address, op_index, filename, line,
				      column, discriminator, false))
		    goto fail_sequence;
		  discriminator = 0;
		  update_address_range (&low_pc, &high_pc, address);
		  break;
		case DW_LNS_advance_pc:
		  advance_address_and_op_index
		    (&address, &op_index, lh,
		     _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end));
		  break;
		case DW_LNS_advance_line:
		  line += _bfd_safe_read_leb128 (abfd, &line_ptr, true, line_end);
		  break;
		case DW_LNS_set_file:
		  {
		    unsigned int filenum = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
		    free (filename);
		    filename = concat_filename (table, filenum);
		  }
		  break;
		case DW_LNS_set_column:
		  column = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
		  break;
		case DW_LNS_negate_stmt:
		  is_stmt = !is_stmt;
		  break;
		case DW_LNS_set_basic_block:
		  break;
		case DW_LNS_const_add_pc:
		  if (lh->line_range == 0)
		    goto fail_sequence;
		  advance_address_and_op_index
		    (&address, &op_index, lh, (255 - lh->opcode_base) / lh->line_range);
		  break;
		case DW_LNS_fixed_advance_pc:
		  address += read_2_bytes (abfd, &line_ptr, line_end);
		  op_index = 0;
		  break;
		default:
		  for (unsigned int i = 0; i < lh->standard_opcode_lengths[op_code]; i++)
		    (void) _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
		  break;
		}
	    }
	}
      free (filename);
      continue;

    fail_sequence:
      _bfd_error_handler (_("DWARF error: mangled line number section"));
      bfd_set_error (bfd_error_bad_value);
      free (filename);
      return false;
    }
  return true;
}

static struct line_info_table*
decode_line_info (struct comp_unit *unit)
{
  bfd *abfd = unit->abfd;
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  struct line_info_table* table = NULL;
  bfd_byte *line_ptr;
  bfd_byte *line_end;
  struct line_head lh = {0};

  if (unit->line_offset == 0 && file->line_table)
    return file->line_table;

  if (!read_section (abfd, &stash->debug_sections[debug_line],
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

  if (!read_line_prologue (unit, &lh, &line_ptr, &line_end))
    return NULL;

  table = (struct line_info_table *) bfd_alloc (abfd, sizeof (*table));
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

  if (!read_file_and_dir_tables (unit, table, &line_ptr, line_end, lh.version))
    goto fail;

  if (!execute_statement_program (unit, table, &lh, line_ptr, line_end))
    goto fail;

  if (unit->line_offset == 0)
    file->line_table = table;

  if (sort_line_sequences (table))
    return table;

fail:
  free_line_info_table_contents (table);
  return NULL;
}

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
  int low, high, mid;

  low = 0;
  high = table->num_sequences;
  while (low < high)
    {
      mid = low + (high - low) / 2;
      struct line_sequence *candidate = &table->sequences[mid];
      if (addr < candidate->low_pc)
	{
	  high = mid;
	}
      else if (addr >= candidate->last_line->address)
	{
	  low = mid + 1;
	}
      else
	{
	  seq = candidate;
	  break;
	}
    }

  if (!seq || !build_line_info_table (table, seq))
    {
      *filename_ptr = NULL;
      return false;
    }

  struct line_info *info = NULL;
  low = 0;
  high = seq->num_lines;
  while (low < high)
    {
      mid = low + (high - low) / 2;
      struct line_info *current = seq->line_info_lookup[mid];
      if (addr < current->address)
	{
	  high = mid;
	}
      else
	{
	  info = current;
	  low = mid + 1;
	}
    }

  if (info && !info->end_sequence && info != seq->last_line)
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
read_debug_ranges (struct comp_unit *unit)
{
  if (!unit || !unit->stash || !unit->file)
    {
      return false;
    }

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  return read_section (unit->abfd, &stash->debug_sections[debug_ranges],
		       file->syms, 0,
		       &file->dwarf_ranges_buffer, &file->dwarf_ranges_size);
}

/* Read in the .debug_rnglists section for future reference.  */

static bool
read_debug_rnglists (struct comp_unit *unit)
{
  if (!unit || !unit->stash || !unit->file)
    {
      return false;
    }

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  return read_section (unit->abfd, &stash->debug_sections[debug_rnglists],
		       file->syms, 0,
		       &file->dwarf_rnglists_buffer, &file->dwarf_rnglists_size);
}

/* Function table functions.  */

static int
compare_lookup_funcinfos (const void * a, const void * b)
{
  const struct lookup_funcinfo * lookup1 = a;
  const struct lookup_funcinfo * lookup2 = b;

  int diff = (lookup1->low_addr > lookup2->low_addr) - (lookup1->low_addr < lookup2->low_addr);
  if (diff != 0)
    {
      return diff;
    }

  diff = (lookup1->high_addr > lookup2->high_addr) - (lookup1->high_addr < lookup2->high_addr);
  if (diff != 0)
    {
      return diff;
    }

  return (lookup1->idx > lookup2->idx) - (lookup1->idx < lookup2->idx);
}

static bool
build_lookup_funcinfo_table (struct comp_unit *unit)
{
  if (unit->lookup_funcinfo_table || unit->number_of_functions == 0)
    return true;

  const size_t number_of_functions = unit->number_of_functions;
  const size_t alloc_size = number_of_functions * sizeof (struct lookup_funcinfo);

  if (number_of_functions > 0 && alloc_size / number_of_functions != sizeof (struct lookup_funcinfo))
    return false;

  struct lookup_funcinfo *new_table = bfd_malloc (alloc_size);
  if (new_table == NULL)
    return false;

  size_t func_index = number_of_functions;
  for (struct funcinfo *current_func = unit->function_table;
       current_func;
       current_func = current_func->prev_func)
    {
      --func_index;
      struct lookup_funcinfo *entry = &new_table[func_index];
      entry->funcinfo = current_func;
      entry->idx = func_index;

      bfd_vma low_addr = current_func->arange.low;
      bfd_vma high_addr = current_func->arange.high;

      for (const struct arange *range = current_func->arange.next;
           range;
           range = range->next)
	{
	  if (range->low < low_addr)
	    low_addr = range->low;
	  if (range->high > high_addr)
	    high_addr = range->high;
	}

      entry->low_addr = low_addr;
      entry->high_addr = high_addr;
    }

  BFD_ASSERT (func_index == 0);

  qsort (new_table, number_of_functions, sizeof (*new_table),
	 compare_lookup_funcinfos);

  bfd_vma high_watermark = new_table[0].high_addr;
  for (size_t i = 1; i < number_of_functions; i++)
    {
      struct lookup_funcinfo *entry = &new_table[i];
      if (entry->high_addr < high_watermark)
	entry->high_addr = high_watermark;
      else
	high_watermark = entry->high_addr;
    }

  unit->lookup_funcinfo_table = new_table;
  return true;
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
  unsigned int number_of_functions = unit->number_of_functions;
  if (number_of_functions == 0)
    {
      return false;
    }

  if (!build_lookup_funcinfo_table (unit))
    {
      return false;
    }

  if (unit->lookup_funcinfo_table[number_of_functions - 1].high_addr < addr)
    {
      return false;
    }

  bfd_size_type first_candidate_idx = number_of_functions;
  {
    bfd_size_type low = 0;
    bfd_size_type high = number_of_functions;
    while (low < high)
      {
	bfd_size_type mid = low + (high - low) / 2;
	const struct lookup_funcinfo *lookup = &unit->lookup_funcinfo_table[mid];

	if (addr < lookup->low_addr)
	  {
	    high = mid;
	  }
	else if (addr >= lookup->high_addr)
	  {
	    low = mid + 1;
	  }
	else
	  {
	    first_candidate_idx = mid;
	    high = mid;
	  }
      }
  }

  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  for (bfd_size_type i = first_candidate_idx; i < number_of_functions; ++i)
    {
      const struct lookup_funcinfo *lookup = &unit->lookup_funcinfo_table[i];
      if (addr < lookup->low_addr)
	{
	  break;
	}

      struct funcinfo *current_func = lookup->funcinfo;
      for (const struct arange *arange = &current_func->arange; arange != NULL; arange = arange->next)
	{
	  if (addr >= arange->low && addr < arange->high)
	    {
	      bfd_vma len = arange->high - arange->low;
	      if (len < best_fit_len
		  || (len == best_fit_len && current_func > best_fit))
		{
		  best_fit = current_func;
		  best_fit_len = len;
		}
	    }
	}
    }

  if (best_fit == NULL)
    {
      return false;
    }

  *function_ptr = best_fit;
  return true;
}

/* If SYM at ADDR is within function table of UNIT, set FILENAME_PTR
   and LINENUMBER_PTR, and return TRUE.  */

static bfd_vma
find_smallest_containing_range (const struct funcinfo *func, bfd_vma addr)
{
  bfd_vma min_len = (bfd_vma) -1;

  for (const struct arange *arange = &func->arange; arange; arange = arange->next)
    {
      if (addr >= arange->low && addr < arange->high)
	{
	  bfd_vma len = arange->high - arange->low;
	  if (len < min_len)
	    {
	      min_len = len;
	    }
	}
    }
  return min_len;
}

static bool
lookup_symbol_in_function_table (struct comp_unit *unit,
				 asymbol *sym,
				 bfd_vma addr,
				 const char **filename_ptr,
				 unsigned int *linenumber_ptr)
{
  if (!unit || !sym || !filename_ptr || !linenumber_ptr)
    {
      return false;
    }

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    {
      return false;
    }

  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  for (struct funcinfo *each = unit->function_table; each; each = each->prev_func)
    {
      if (!each->file || !each->name || strstr (name, each->name) == NULL)
	{
	  continue;
	}

      bfd_vma current_len = find_smallest_containing_range (each, addr);
      if (current_len < best_fit_len)
	{
	  best_fit = each;
	  best_fit_len = current_len;
	}
    }

  if (best_fit)
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
lookup_symbol_in_variable_table (struct comp_unit *unit,
				 asymbol *sym,
				 bfd_vma addr,
				 const char **filename_ptr,
				 unsigned int *linenumber_ptr)
{
  if (!unit || !sym || !filename_ptr || !linenumber_ptr)
    {
      return false;
    }

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    {
      return false;
    }

  for (struct varinfo *each = unit->variable_table; each; each = each->prev_var)
    {
      if (each->addr == addr
	  && !each->stack
	  && each->file
	  && each->name
	  && strstr (name, each->name))
	{
	  *filename_ptr = each->file;
	  *linenumber_ptr = each->line;
	  return true;
	}
    }

  return false;
}

static struct comp_unit *stash_comp_unit (struct dwarf2_debug *,
					  struct dwarf2_debug_file *);
static bool comp_unit_maybe_decode_line_info (struct comp_unit *);

#define MAX_ABSTRACT_INSTANCE_RECURSION 100

static bool
find_abstract_instance (struct comp_unit *unit,
			struct attribute *attr_ptr,
			unsigned int recur_count,
			const char **pname,
			bool *is_linkage,
			char **filename_ptr,
			int *linenumber_ptr);

static bool
process_abstract_instance_attributes (struct comp_unit *unit,
				      bfd_byte *info_ptr,
				      bfd_byte *info_ptr_end,
				      unsigned int recur_count,
				      const char **pname,
				      bool *is_linkage,
				      char **filename_ptr,
				      int *linenumber_ptr)
{
  bfd *abfd = unit->abfd;
  unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false,
						     info_ptr_end);

  if (abbrev_number == 0)
    return true;

  struct abbrev_info *abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"),
			  abbrev_number);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      bfd_byte *next_info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit,
						info_ptr, info_ptr_end);
      if (next_info_ptr == NULL)
	break;
      info_ptr = next_info_ptr;

      switch (attr.name)
	{
	case DW_AT_name:
	  if (*pname == NULL && is_str_form (&attr))
	    {
	      *pname = attr.u.str;
	      if (mangle_style (unit->lang) == 0)
		*is_linkage = true;
	    }
	  break;
	case DW_AT_specification:
	  if (is_int_form (&attr)
	      && !find_abstract_instance (unit, &attr, recur_count + 1, pname,
					  is_linkage, filename_ptr,
					  linenumber_ptr))
	    return false;
	  break;
	case DW_AT_linkage_name:
	case DW_AT_MIPS_linkage_name:
	  if (is_str_form (&attr))
	    {
	      *pname = attr.u.str;
	      *is_linkage = true;
	    }
	  break;
	case DW_AT_decl_file:
	  if (!comp_unit_maybe_decode_line_info (unit))
	    return false;
	  if (is_int_form (&attr))
	    {
	      free (*filename_ptr);
	      *filename_ptr = concat_filename (unit->line_table, attr.u.val);
	    }
	  break;
	case DW_AT_decl_line:
	  if (is_int_form (&attr))
	    *linenumber_ptr = attr.u.val;
	  break;
	default:
	  break;
	}
    }
  return true;
}

static struct comp_unit *
find_cu_for_ref (struct comp_unit *start_unit, bfd_byte *ref_ptr,
		 bool is_alt_ref)
{
  if (ref_ptr >= start_unit->info_ptr_unit && ref_ptr < start_unit->end_ptr)
    return start_unit;

  struct addr_range range = { ref_ptr, ref_ptr };
  splay_tree_node v =
    splay_tree_lookup (start_unit->file->comp_unit_tree,
		       (splay_tree_key) &range);
  if (v != NULL)
    return (struct comp_unit *) v->value;

  struct cu_file *cu_source =
    is_alt_ref ? &start_unit->stash->alt : &start_unit->stash->f;
  struct comp_unit *u;
  while ((u = stash_comp_unit (start_unit->stash, cu_source)) != NULL)
    {
      if (ref_ptr >= u->info_ptr_unit && ref_ptr < u->end_ptr)
	return u;
    }

  return NULL;
}

static bool
resolve_die_reference (struct comp_unit **p_unit,
		       struct attribute *attr_ptr,
		       bfd_byte **p_info_ptr, bfd_byte **p_info_ptr_end)
{
  uint64_t die_ref = attr_ptr->u.val;

  if (attr_ptr->form == DW_FORM_ref_addr
      || attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      struct comp_unit *search_cu = *p_unit;
      bfd_byte *ref_ptr;
      bool is_alt_ref = (attr_ptr->form == DW_FORM_GNU_ref_alt);

      if (is_alt_ref)
	{
	  bool first_time = (*p_unit)->stash->alt.dwarf_info_buffer == NULL;
	  ref_ptr = read_alt_indirect_ref (*p_unit, die_ref);
	  if (first_time)
	    (*p_unit)->stash->alt.info_ptr
	      = (*p_unit)->stash->alt.dwarf_info_buffer;
	  if (ref_ptr == NULL)
	    {
	      _bfd_error_handler (
		_("DWARF error: unable to read alt ref %" PRIu64), die_ref);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  if ((*p_unit)->stash->alt.all_comp_units)
	    search_cu = (*p_unit)->stash->alt.all_comp_units;
	}
      else
	{
	  if (die_ref == 0)
	    {
	      *p_info_ptr = NULL;
	      return true;
	    }
	  if (die_ref >= (*p_unit)->file->dwarf_info_size)
	    {
	      _bfd_error_handler (_("DWARF error: invalid abstract instance DIE ref"));
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  ref_ptr = (*p_unit)->file->dwarf_info_buffer + die_ref;
	}

      *p_unit = find_cu_for_ref (search_cu, ref_ptr, is_alt_ref);
      if (*p_unit == NULL)
	{
	  _bfd_error_handler (
	    _("DWARF error: unable to locate abstract instance DIE ref %" PRIu64),
	    die_ref);
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
      *p_info_ptr = ref_ptr;
      *p_info_ptr_end = (*p_unit)->end_ptr;
    }
  else
    {
      size_t cu_size = (*p_unit)->end_ptr - (*p_unit)->info_ptr_unit;
      if (die_ref == 0 || die_ref >= cu_size)
	{
	  _bfd_error_handler (_("DWARF error: invalid abstract instance DIE ref"));
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
      *p_info_ptr = (*p_unit)->info_ptr_unit + die_ref;
      *p_info_ptr_end = (*p_unit)->end_ptr;
    }
  return true;
}

static bool
find_abstract_instance (struct comp_unit *unit,
			struct attribute *attr_ptr,
			unsigned int recur_count,
			const char **pname,
			bool *is_linkage,
			char **filename_ptr,
			int *linenumber_ptr)
{
  if (recur_count >= MAX_ABSTRACT_INSTANCE_RECURSION)
    {
      _bfd_error_handler (_("DWARF error: abstract instance recursion detected"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  struct comp_unit *die_cu = unit;
  bfd_byte *die_info_ptr;
  bfd_byte *die_info_ptr_end;

  if (!resolve_die_reference (&die_cu, attr_ptr, &die_info_ptr,
			      &die_info_ptr_end))
    return false;

  if (die_info_ptr == NULL)
    return true;

  return process_abstract_instance_attributes (
    die_cu, die_info_ptr, die_info_ptr_end, recur_count, pname, is_linkage,
    filename_ptr, linenumber_ptr);
}

static bool
read_ranges (struct comp_unit *unit, struct arange *arange,
	     struct trie_node **trie_root, uint64_t offset)
{
  bfd_vma base_address = unit->base_address;

  if (!unit->file->dwarf_ranges_buffer)
    {
      if (!read_debug_ranges (unit))
	{
	  return false;
	}
    }

  if (offset > unit->file->dwarf_ranges_size)
    {
      return false;
    }

  bfd_byte *ranges_ptr = unit->file->dwarf_ranges_buffer + offset;
  const bfd_byte *ranges_end =
    unit->file->dwarf_ranges_buffer + unit->file->dwarf_ranges_size;
  const size_t entry_size = 2u * unit->addr_size;

  for (;;)
    {
      if ((size_t) (ranges_end - ranges_ptr) < entry_size)
	{
	  return false;
	}

      const bfd_vma low_pc = read_address (unit, &ranges_ptr, ranges_end);
      const bfd_vma high_pc = read_address (unit, &ranges_ptr, ranges_end);

      if (low_pc == 0 && high_pc == 0)
	{
	  break;
	}

      if (low_pc == (bfd_vma) -1 && high_pc != (bfd_vma) -1)
	{
	  base_address = high_pc;
	}
      else
	{
	  if (!arange_add (unit, arange, trie_root,
			   base_address + low_pc, base_address + high_pc))
	    {
	      return false;
	    }
	}
    }

  return true;
}

enum rnglist_parse_result
{
  RPL_ERROR,
  RPL_END_OF_LIST,
  RPL_RANGE_PRODUCED,
  RPL_BASE_ADDRESS_SET
};

static enum rnglist_parse_result
parse_one_rnglist_entry (struct comp_unit *unit, bfd_byte **p_rngs_ptr,
			 bfd_byte *rngs_end, bfd_vma *p_base_address,
			 bfd_vma *p_low_pc, bfd_vma *p_high_pc)
{
  enum dwarf_range_list_entry rlet;

  if (*p_rngs_ptr >= rngs_end)
    return RPL_ERROR;

  rlet = read_1_byte (unit->abfd, p_rngs_ptr, rngs_end);

  switch (rlet)
    {
    case DW_RLE_end_of_list:
      return RPL_END_OF_LIST;

    case DW_RLE_base_address:
      if ((size_t) (rngs_end - *p_rngs_ptr) < unit->addr_size)
	return RPL_ERROR;
      *p_base_address = read_address (unit, p_rngs_ptr, rngs_end);
      return RPL_BASE_ADDRESS_SET;

    case DW_RLE_start_length:
      if ((size_t) (rngs_end - *p_rngs_ptr) < unit->addr_size)
	return RPL_ERROR;
      *p_low_pc = read_address (unit, p_rngs_ptr, rngs_end);
      *p_high_pc = *p_low_pc
	+ _bfd_safe_read_leb128 (unit->abfd, p_rngs_ptr, false, rngs_end);
      break;

    case DW_RLE_offset_pair:
      *p_low_pc = *p_base_address
	+ _bfd_safe_read_leb128 (unit->abfd, p_rngs_ptr, false, rngs_end);
      *p_high_pc = *p_base_address
	+ _bfd_safe_read_leb128 (unit->abfd, p_rngs_ptr, false, rngs_end);
      break;

    case DW_RLE_start_end:
      if ((size_t) (rngs_end - *p_rngs_ptr) < 2u * unit->addr_size)
	return RPL_ERROR;
      *p_low_pc = read_address (unit, p_rngs_ptr, rngs_end);
      *p_high_pc = read_address (unit, p_rngs_ptr, rngs_end);
      break;

    case DW_RLE_base_addressx:
    case DW_RLE_startx_endx:
    case DW_RLE_startx_length:
    default:
      return RPL_ERROR;
    }

  return RPL_RANGE_PRODUCED;
}

static bool
read_rnglists (struct comp_unit *unit, struct arange *arange,
	       struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *rngs_ptr;
  bfd_byte *rngs_end;
  bfd_vma base_address = unit->base_address;

  if (!unit->file->dwarf_rnglists_buffer)
    {
      if (!read_debug_rnglists (unit))
	return false;
    }

  rngs_ptr = unit->file->dwarf_rnglists_buffer + offset;
  if (rngs_ptr < unit->file->dwarf_rnglists_buffer)
    return false;
  rngs_end = unit->file->dwarf_rnglists_buffer
    + unit->file->dwarf_rnglists_size;

  for (;;)
    {
      bfd_vma low_pc;
      bfd_vma high_pc;
      enum rnglist_parse_result result =
	parse_one_rnglist_entry (unit, &rngs_ptr, rngs_end, &base_address,
				 &low_pc, &high_pc);

      switch (result)
	{
	case RPL_END_OF_LIST:
	  return true;

	case RPL_BASE_ADDRESS_SET:
	  break;

	case RPL_RANGE_PRODUCED:
	  if (!arange_add (unit, arange, trie_root, low_pc, high_pc))
	    return false;
	  break;

	case RPL_ERROR:
	default:
	  return false;
	}
    }
}

static bool
read_rangelist (struct comp_unit *unit, struct arange *arange,
		struct trie_node **trie_root, uint64_t offset)
{
  if (!unit)
    {
      return false;
    }

  if (unit->version <= 4)
    {
      return read_ranges (unit, arange, trie_root, offset);
    }

  return read_rnglists (unit, arange, trie_root, offset);
}

static struct funcinfo *
lookup_func_by_offset(uint64_t offset, struct funcinfo *current_func)
{
    while (current_func != NULL) {
        if (current_func->unit_offset == offset) {
            return current_func;
        }
        current_func = current_func->prev_func;
    }
    return NULL;
}

static const struct varinfo *lookup_var_by_offset(uint64_t offset, const struct varinfo *table)
{
    for (const struct varinfo *current = table; current != NULL; current = current->prev_var) {
        if (current->unit_offset == offset) {
            return current;
        }
    }
    return NULL;
}


/* DWARF2 Compilation unit functions.  */

static struct funcinfo *
reverse_funcinfo_list (struct funcinfo *head)
{
  struct funcinfo *previous = NULL;
  struct funcinfo *current = head;
  struct funcinfo *next = NULL;

  while (current != NULL)
    {
      next = current->prev_func;
      current->prev_func = previous;
      previous = current;
      current = next;
    }

  return previous;
}

static struct varinfo *
reverse_varinfo_list (struct varinfo *head)
{
  struct varinfo *previous_node = NULL;
  struct varinfo *current_node = head;
  struct varinfo *next_node = NULL;

  while (current_node != NULL)
    {
      next_node = current_node->prev_var;
      current_node->prev_var = previous_node;
      previous_node = current_node;
      current_node = next_node;
    }

  return previous_node;
}

/* Scan over each die in a comp. unit looking for functions to add
   to the function table and variables to the variable table.  */

#define INITIAL_NESTED_FUNCS_SIZE 32

struct die_info
{
  struct abbrev_info *abbrev;
  uint64_t offset;
};

struct nest_funcinfo
{
  struct funcinfo *func;
};

static bool
resize_nested_funcs_if_needed (int nesting_level,
			       struct nest_funcinfo **nested_funcs,
			       int *nested_funcs_size)
{
  if (nesting_level >= *nested_funcs_size)
    {
      int new_size = *nested_funcs_size * 2;
      struct nest_funcinfo *tmp = (struct nest_funcinfo *)
	bfd_realloc (*nested_funcs, new_size * sizeof (**nested_funcs));
      if (tmp == NULL)
	return false;
      *nested_funcs = tmp;
      *nested_funcs_size = new_size;
    }
  return true;
}

static bool
add_func_to_table_pass1 (struct comp_unit *unit, struct abbrev_info *abbrev,
			 uint64_t offset, int nesting_level,
			 struct nest_funcinfo *nested_funcs)
{
  struct funcinfo *func = (struct funcinfo *)
    bfd_zalloc (unit->abfd, sizeof (struct funcinfo));
  if (func == NULL)
    return false;

  func->tag = abbrev->tag;
  func->prev_func = unit->function_table;
  func->unit_offset = offset;
  unit->function_table = func;
  unit->number_of_functions++;
  BFD_ASSERT (!unit->cached);

  if (func->tag == DW_TAG_inlined_subroutine)
    {
      for (int i = nesting_level; i-- != 0;)
	{
	  if (nested_funcs[i].func)
	    {
	      func->caller_func = nested_funcs[i].func;
	      break;
	    }
	}
    }
  nested_funcs[nesting_level].func = func;
  return true;
}

static bool
add_var_to_table_pass1 (struct comp_unit *unit, struct abbrev_info *abbrev,
			uint64_t offset)
{
  struct varinfo *var = (struct varinfo *)
    bfd_zalloc (unit->abfd, sizeof (struct varinfo));
  if (var == NULL)
    return false;

  var->tag = abbrev->tag;
  var->stack = true;
  var->prev_var = unit->variable_table;
  var->unit_offset = offset;
  unit->variable_table = var;
  return true;
}

static bool
skip_attributes (bfd_byte **info_ptr, bfd_byte *info_ptr_end,
		 struct comp_unit *unit, const struct abbrev_info *abbrev)
{
  for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      *info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit,
				  *info_ptr, info_ptr_end);
      if (*info_ptr == NULL)
	return false;
    }
  return true;
}

static bool
read_abbrev (struct die_info *die, bfd_byte **info_ptr, bfd_byte *info_ptr_end,
	     struct comp_unit *unit, bool *is_null_entry)
{
  if (*info_ptr >= info_ptr_end)
    return false;

  die->offset = *info_ptr - unit->info_ptr_unit;
  unsigned int abbrev_number =
    _bfd_safe_read_leb128 (unit->abfd, info_ptr, false, info_ptr_end);

  *is_null_entry = (abbrev_number == 0);
  if (*is_null_entry)
    return true;

  die->abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
  if (die->abbrev == NULL)
    {
      static unsigned int previous_failed_abbrev = -1U;
      if (abbrev_number != previous_failed_abbrev)
	{
	  _bfd_error_handler (_("DWARF error: could not find abbrev number %u"),
			      abbrev_number);
	  previous_failed_abbrev = abbrev_number;
	}
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
perform_first_pass (struct comp_unit *unit, struct nest_funcinfo **nested_funcs,
		    int *nested_funcs_size)
{
  bfd_byte *info_ptr = unit->first_child_die_ptr;
  bfd_byte *info_ptr_end = unit->end_ptr;
  int nesting_level = 0;

  while (nesting_level >= 0)
    {
      struct die_info die;
      bool is_null_entry;

      if (!read_abbrev (&die, &info_ptr, info_ptr_end, unit, &is_null_entry))
	return false;

      if (is_null_entry)
	{
	  nesting_level--;
	  continue;
	}

      if (die.abbrev->tag == DW_TAG_subprogram
	  || die.abbrev->tag == DW_TAG_entry_point
	  || die.abbrev->tag == DW_TAG_inlined_subroutine)
	{
	  if (!add_func_to_table_pass1 (unit, die.abbrev, die.offset,
					nesting_level, *nested_funcs))
	    return false;
	}
      else if (die.abbrev->tag == DW_TAG_variable
	       || die.abbrev->tag == DW_TAG_member)
	{
	  if (!add_var_to_table_pass1 (unit, die.abbrev, die.offset))
	    return false;
	  (*nested_funcs)[nesting_level].func = 0;
	}
      else
	{
	  (*nested_funcs)[nesting_level].func = 0;
	}

      if (!skip_attributes (&info_ptr, info_ptr_end, unit, die.abbrev))
	return false;

      if (die.abbrev->has_children)
	{
	  nesting_level++;
	  if (!resize_nested_funcs_if_needed (nesting_level, nested_funcs,
					      nested_funcs_size))
	    return false;
	  (*nested_funcs)[nesting_level].func = 0;
	}
    }
  return true;
}

static struct funcinfo *
get_func_for_offset (uint64_t offset, struct comp_unit *unit,
		     struct funcinfo *last_func)
{
  if (last_func && last_func->prev_func
      && last_func->prev_func->unit_offset == offset)
    return last_func->prev_func;
  return lookup_func_by_offset (offset, unit->function_table);
}

static struct varinfo *
get_var_for_offset (uint64_t offset, struct comp_unit *unit,
		    struct varinfo *last_var)
{
  if (last_var && last_var->prev_var
      && last_var->prev_var->unit_offset == offset)
    return last_var->prev_var;
  return lookup_var_by_offset (offset, unit->variable_table);
}

static bool
process_func_attribute (struct funcinfo *func, struct comp_unit *unit,
			const struct attribute *attr, bfd_vma *low_pc,
			bfd_vma *high_pc, bool *high_pc_relative)
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
	  && !find_abstract_instance (unit, attr, 0, &func->name,
				      &func->is_linkage, &func->file,
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
	*low_pc = attr->u.val;
      break;

    case DW_AT_high_pc:
      if (is_int_form (attr))
	{
	  *high_pc = attr->u.val;
	  *high_pc_relative = (attr->form != DW_FORM_addr);
	}
      break;

    case DW_AT_ranges:
      if (is_int_form (attr)
	  && !read_rangelist (unit, &func->arange, &unit->file->trie_root,
			      attr->u.val))
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
process_var_location_attribute (struct varinfo *var, struct comp_unit *unit,
				const struct attribute *attr)
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
	    var->addr = bfd_get (unit->addr_size * 8, unit->abfd,
				 attr->u.blk->data + 1);
	}
      break;
    default:
      break;
    }
}

static void
process_var_attribute (struct varinfo *var, struct comp_unit *unit,
		       const struct attribute *attr)
{
  switch (attr->name)
    {
    case DW_AT_specification:
      if (is_int_form (attr) && attr->u.val)
	{
	  bool is_linkage;
	  if (!find_abstract_instance (unit, attr, 0, &var->name, &is_linkage,
				       &var->file, &var->line))
	    _bfd_error_handler (_("DWARF error: could not find "
				  "variable specification "
				  "at offset 0x%lx"),
				(unsigned long) attr->u.val);
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
      process_var_location_attribute (var, unit, attr);
      break;

    default:
      break;
    }
}

static bool
perform_second_pass (struct comp_unit *unit)
{
  bfd_byte *info_ptr = unit->first_child_die_ptr;
  bfd_byte *info_ptr_end = unit->end_ptr;
  int nesting_level = 0;
  struct funcinfo *last_func = NULL;
  struct varinfo *last_var = NULL;

  while (nesting_level >= 0)
    {
      if (info_ptr >= info_ptr_end)
	return false;

      uint64_t current_offset = info_ptr - unit->info_ptr_unit;
      unsigned int abbrev_number =
	_bfd_safe_read_leb128 (unit->abfd, &info_ptr, false, info_ptr_end);

      if (abbrev_number == 0)
	{
	  nesting_level--;
	  continue;
	}

      struct abbrev_info *abbrev = lookup_abbrev (abbrev_number,
						  unit->abbrevs);
      BFD_ASSERT (abbrev != NULL);

      struct funcinfo *func = NULL;
      struct varinfo *var = NULL;

      if (abbrev->tag == DW_TAG_subprogram
	  || abbrev->tag == DW_TAG_entry_point
	  || abbrev->tag == DW_TAG_inlined_subroutine)
	{
	  func = get_func_for_offset (current_offset, unit, last_func);
	  if (func == NULL)
	    return false;
	  last_func = func;
	}
      else if (abbrev->tag == DW_TAG_variable
	       || abbrev->tag == DW_TAG_member)
	{
	  var = get_var_for_offset (current_offset, unit, last_var);
	  if (var == NULL)
	    return false;
	  last_var = var;
	}

      bfd_vma low_pc = 0;
      bfd_vma high_pc = 0;
      bool high_pc_relative = false;

      for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
	{
	  struct attribute attr;
	  info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit,
				     info_ptr, info_ptr_end);
	  if (info_ptr == NULL)
	    return false;

	  if (func)
	    {
	      if (!process_func_attribute (func, unit, &attr, &low_pc, &high_pc,
					   &high_pc_relative))
		return false;
	    }
	  else if (var)
	    {
	      process_var_attribute (var, unit, &attr);
	    }
	}

      if (func && high_pc != 0)
	{
	  if (high_pc_relative)
	    high_pc += low_pc;
	  if (!arange_add (unit, &func->arange, &unit->file->trie_root,
			   low_pc, high_pc))
	    return false;
	}

      if (abbrev->has_children)
	nesting_level++;
    }
  return true;
}

static bool
scan_unit_for_symbols (struct comp_unit *unit)
{
  struct nest_funcinfo *nested_funcs;
  int nested_funcs_size = INITIAL_NESTED_FUNCS_SIZE;
  bool ok = false;

  nested_funcs = (struct nest_funcinfo *)
    bfd_malloc (nested_funcs_size * sizeof (*nested_funcs));
  if (nested_funcs == NULL)
    return false;

  nested_funcs[0].func = 0;

  if (perform_first_pass (unit, &nested_funcs, &nested_funcs_size))
    {
      unit->function_table = reverse_funcinfo_list (unit->function_table);
      unit->variable_table = reverse_varinfo_list (unit->variable_table);

      if (perform_second_pass (unit))
	{
	  unit->function_table = reverse_funcinfo_list (unit->function_table);
	  unit->variable_table = reverse_varinfo_list (unit->variable_table);
	  ok = true;
	}
    }

  free (nested_funcs);
  return ok;
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
      *high_pc_relative = (attr->form != DW_FORM_addr);
      break;

    case DW_AT_ranges:
      if (!read_rangelist (unit, &unit->arange,
			   &unit->file->trie_root, attr->u.val))
	return;
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
	  if (comp_dir)
	    {
	      char *cp = strchr (comp_dir, ':');
	      if (cp && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
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
  struct comp_unit* unit = NULL;
  struct abbrev_info** abbrevs;
  struct attribute *str_addrp = NULL;
  size_t str_count = 0;
  size_t str_alloc = 0;
  bfd *abfd = file->bfd_ptr;
  bfd_byte *end_ptr = info_ptr + unit_length;
  unsigned int version;
  enum dwarf_unit_type unit_type;
  unsigned int addr_size;
  uint64_t abbrev_offset;

  version = read_2_bytes (abfd, &info_ptr, end_ptr);
  if (version == 0)
    return NULL;

  if (version < 2 || version > 5)
    {
      _bfd_error_handler
	(_("DWARF error: found dwarf version '%u', this reader"
	   " only handles version 2, 3, 4 and 5 information"), version);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  if (version >= 5)
    {
      unit_type = read_1_byte (abfd, &info_ptr, end_ptr);
      addr_size = read_1_byte (abfd, &info_ptr, end_ptr);
    }
  else
    {
      unit_type = DW_UT_compile;
      addr_size = 0;
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
	 addr_size, (unsigned int) sizeof (bfd_vma));
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

  unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, end_ptr);
  if (!abbrev_number)
    return NULL;

  struct abbrev_info *abbrev = lookup_abbrev (abbrev_number, abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"), abbrev_number);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  unit = (struct comp_unit *) bfd_zalloc (abfd, sizeof (struct comp_unit));
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

  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bool high_pc_relative = false;
  bool is_compile_unit_die = (abbrev->tag == DW_TAG_compile_unit);
  unsigned int i;

  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit, info_ptr, end_ptr);
      if (info_ptr == NULL)
	goto fail;

      if ((unit->dwarf_str_offset == 0 && is_strx_form (attr.form))
	  || (unit->dwarf_addr_offset == 0 && is_addrx_form (attr.form)))
	{
	  if (str_count >= str_alloc)
	    {
	      size_t new_alloc = (str_alloc == 0) ? 16 : str_alloc * 2;
	      struct attribute *new_str_addrp = bfd_realloc (str_addrp, new_alloc * sizeof (*str_addrp));
	      if (new_str_addrp == NULL)
		goto fail;
	      str_addrp = new_str_addrp;
	      str_alloc = new_alloc;
	    }
	  str_addrp[str_count++] = attr;
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
	      if (is_compile_unit_die)
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
	      && !read_rangelist (unit, &unit->arange, &unit->file->trie_root, attr.u.val))
	    goto fail;
	  break;
	case DW_AT_comp_dir:
	  if (!is_str_form (&attr))
	    {
	      _bfd_error_handler (_("DWARF error: DW_AT_comp_dir attribute encountered with a non-string form"));
	      unit->comp_dir = NULL;
	    }
	  else
	    {
	      char *comp_dir = attr.u.str;
	      /* Irix 6.2 native cc prepends <machine>.: to the compilation directory. */
	      char *cp = strchr (comp_dir, ':');
	      if (cp && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
		comp_dir = cp + 1;
	      unit->comp_dir = comp_dir;
	    }
	  break;
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
    reread_attribute (unit, &str_addrp[i], &low_pc, &high_pc, &high_pc_relative, is_compile_unit_die);

  if (high_pc != 0)
    {
      if (high_pc_relative)
	high_pc += low_pc;
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root, low_pc, high_pc))
	goto fail;
    }

  unit->first_child_die_ptr = info_ptr;
  free (str_addrp);
  return unit;

 fail:
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
  if (!unit || unit->error)
  {
    return false;
  }

  if (unit->arange.high == 0 || unit->line_table == NULL)
  {
    return true;
  }

  for (const struct arange *arange = &unit->arange; arange; arange = arange->next)
  {
    if (addr >= arange->low && addr < arange->high)
    {
      return true;
    }
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
  if (!comp_unit_maybe_decode_line_info (unit))
    {
      return false;
    }

  *function_ptr = NULL;
  bool found_func = lookup_address_in_function_table (unit, addr, function_ptr);

  if (found_func && (*function_ptr)->tag == DW_TAG_inlined_subroutine)
    {
      unit->stash->inliner_chain = *function_ptr;
    }

  bool found_line = lookup_address_in_line_info_table (unit->line_table, addr,
						       filename_ptr,
						       linenumber_ptr,
						       discriminator_ptr);

  return found_line || found_func;
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
    goto set_error_and_fail;

  unit->line_table = decode_line_info (unit);
  if (!unit->line_table)
    goto set_error_and_fail;

  if (unit->first_child_die_ptr < unit->end_ptr
      && !scan_unit_for_symbols (unit))
    goto set_error_and_fail;

  return true;

set_error_and_fail:
  unit->error = 1;
  return false;
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
    {
      return false;
    }

  if (sym->flags & BSF_FUNCTION)
    {
      return lookup_symbol_in_function_table (unit, sym, addr,
					      filename_ptr,
					      linenumber_ptr);
    }

  return lookup_symbol_in_variable_table (unit, sym, addr,
					  filename_ptr,
					  linenumber_ptr);
}

/* Extract all interesting funcinfos and varinfos of a compilation
   unit into hash tables for faster lookup.  Returns TRUE if no
   errors were enountered; FALSE otherwise.  */

static bool
hash_comp_unit_functions (struct comp_unit *unit,
			  struct info_hash_table *funcinfo_hash_table)
{
  /* To preserve the original search order, we visit the function
     infos in the reversed order of the list. We reverse the list first,
     traverse it, and then reverse it back to restore the original order. */
  unit->function_table = reverse_funcinfo_list (unit->function_table);

  for (struct funcinfo *each_func = unit->function_table;
       each_func;
       each_func = each_func->prev_func)
    {
      /* Skip nameless functions. */
      if (each_func->name)
	{
	  /* Name string is already in a permanent buffer, no copy needed. */
	  if (!insert_info_hash_table (funcinfo_hash_table, each_func->name,
				       (void *) each_func, false))
	    {
	      unit->function_table = reverse_funcinfo_list (unit->function_table);
	      return false;
	    }
	}
    }

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  return true;
}

static bool
hash_comp_unit_variables (struct comp_unit *unit,
			  struct info_hash_table *varinfo_hash_table)
{
  /* We do the same list reversal for variable infos. */
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  for (struct varinfo *each_var = unit->variable_table;
       each_var;
       each_var = each_var->prev_var)
    {
      /* Skip stack vars and vars with no files or names. */
      if (!each_var->stack
	  && each_var->file != NULL
	  && each_var->name != NULL)
	{
	  /* Name string is already in a permanent buffer, no copy needed. */
	  if (!insert_info_hash_table (varinfo_hash_table, each_var->name,
				       (void *) each_var, false))
	    {
	      unit->variable_table = reverse_varinfo_list (unit->variable_table);
	      return false;
	    }
	}
    }

  unit->variable_table = reverse_varinfo_list (unit->variable_table);
  return true;
}

static bool
comp_unit_hash_info (struct dwarf2_debug *stash,
		     struct comp_unit *unit,
		     struct info_hash_table *funcinfo_hash_table,
		     struct info_hash_table *varinfo_hash_table)
{
  BFD_ASSERT (stash->info_hash_status != STASH_INFO_HASH_DISABLED);
  BFD_ASSERT (!unit->cached);

  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  if (!hash_comp_unit_functions (unit, funcinfo_hash_table))
    return false;

  if (!hash_comp_unit_variables (unit, varinfo_hash_table))
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

static asection *
find_debug_info (bfd *abfd, const struct dwarf_debug_section *debug_sections,
                 asection *after_sec)
{
  asection *sec;
  const char *uncompressed_name = debug_sections[debug_info].uncompressed_name;
  const char *compressed_name = debug_sections[debug_info].compressed_name;

  if (after_sec == NULL)
    {
      sec = bfd_get_section_by_name (abfd, uncompressed_name);
      if (sec != NULL && (sec->flags & SEC_HAS_CONTENTS) != 0)
        return sec;

      if (compressed_name != NULL)
        {
          sec = bfd_get_section_by_name (abfd, compressed_name);
          if (sec != NULL && (sec->flags & SEC_HAS_CONTENTS) != 0)
            return sec;
        }
    }

  for (sec = after_sec ? after_sec->next : abfd->sections;
       sec != NULL;
       sec = sec->next)
    {
      if ((sec->flags & SEC_HAS_CONTENTS) == 0)
        continue;

      if (strcmp (sec->name, uncompressed_name) == 0)
        return sec;

      if (compressed_name != NULL && strcmp (sec->name, compressed_name) == 0)
        return sec;

      if (startswith (sec->name, GNU_LINKONCE_INFO))
        return sec;
    }

  return NULL;
}

/* Transfer VMAs from object file to separate debug file.  */

static void
set_debug_vma (bfd *orig_bfd, bfd *debug_bfd)
{
  if (!orig_bfd || !debug_bfd)
    {
      return;
    }

  asection *orig_sec = orig_bfd->sections;
  asection *debug_sec = debug_bfd->sections;

  while (orig_sec && debug_sec)
    {
      if ((debug_sec->flags & SEC_DEBUGGING) != 0)
	{
	  break;
	}

      if (orig_sec->name && debug_sec->name
	  && strcmp (orig_sec->name, debug_sec->name) == 0)
	{
	  debug_sec->output_section = orig_sec->output_section;
	  debug_sec->output_offset = orig_sec->output_offset;
	  debug_sec->vma = orig_sec->vma;
	}

      orig_sec = orig_sec->next;
      debug_sec = debug_sec->next;
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
    {
      return;
    }

  if (*sec == NULL)
    {
      *syms = stash->f.syms;
      return;
    }

  asection *s;
  asection *d;
  for (s = abfd->sections, d = stash->f.bfd_ptr->sections;
       s != NULL && d != NULL;
       s = s->next, d = d->next)
    {
      if ((d->flags & SEC_DEBUGGING) != 0)
	{
	  break;
	}

      if (s == *sec
	  && s->name != NULL
	  && d->name != NULL
	  && strcmp (s->name, d->name) == 0)
	{
	  *sec = d;
	  *syms = stash->f.syms;
	  break;
	}
    }
}

/* Unset vmas for adjusted sections in STASH.  */

static void
unset_sections (struct dwarf2_debug *stash)
{
  for (int i = 0; i < stash->adjusted_section_count; i++)
    {
      struct adjusted_section *p = &stash->adjusted_sections[i];
      p->section->vma = p->orig_vma;
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
is_section_to_be_processed (const asection *sect, const bfd *abfd,
                            const bfd *orig_bfd,
                            const char *debug_info_name,
                            bool *is_debug_info_out)
{
  if (sect->output_section != NULL
      && sect->output_section != sect
      && (sect->flags & SEC_DEBUGGING) == 0)
    {
      return false;
    }

  bool is_debug = (strcmp (sect->name, debug_info_name) == 0
                   || startswith (sect->name, GNU_LINKONCE_INFO));
  if (is_debug_info_out)
    {
      *is_debug_info_out = is_debug;
    }

  bool is_alloc_in_orig = (sect->flags & SEC_ALLOC) != 0 && abfd == orig_bfd;

  return is_alloc_in_orig || is_debug;
}

static bool
place_sections (bfd *orig_bfd, struct dwarf2_debug *stash)
{
  if (stash->adjusted_section_count != 0)
    {
      if (stash->adjusted_section_count > 0)
        {
          for (int i = 0; i < stash->adjusted_section_count; i++)
            {
              stash->adjusted_sections[i].section->vma =
                stash->adjusted_sections[i].adj_vma;
            }
        }
      return true;
    }

  const char *debug_info_name = stash->debug_sections[debug_info].uncompressed_name;
  bfd *bfds_to_scan[] = { orig_bfd, stash->f.bfd_ptr };
  int num_bfds = (orig_bfd == stash->f.bfd_ptr) ? 1 : 2;
  int section_count = 0;

  for (int i = 0; i < num_bfds; i++)
    {
      bfd *abfd = bfds_to_scan[i];
      for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
        {
          if (is_section_to_be_processed (sect, abfd, orig_bfd, debug_info_name, NULL))
            {
              section_count++;
            }
        }
    }

  if (section_count > 1)
    {
      size_t amt = (size_t) section_count * sizeof (struct adjusted_section);
      struct adjusted_section *p =
        (struct adjusted_section *) bfd_malloc (amt);
      if (p == NULL)
        {
          return false;
        }

      stash->adjusted_sections = p;
      stash->adjusted_section_count = section_count;

      bfd_vma last_vma = 0;
      bfd_vma last_dwarf = 0;

      for (int i = 0; i < num_bfds; i++)
        {
          bfd *abfd = bfds_to_scan[i];
          for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
            {
              bool is_debug_info;
              if (!is_section_to_be_processed (sect, abfd, orig_bfd, debug_info_name, &is_debug_info))
                {
                  continue;
                }

              bfd_size_type sz = sect->rawsize ? sect->rawsize : sect->size;
              p->section = sect;
              p->orig_vma = sect->vma;

              bfd_vma *vma_ptr = is_debug_info ? &last_dwarf : &last_vma;
              bfd_vma align_mask = ((bfd_vma) 1 << sect->alignment_power) - 1;

              *vma_ptr = (*vma_ptr + align_mask) & ~align_mask;
              sect->vma = *vma_ptr;
              *vma_ptr += sz;

              p->adj_vma = sect->vma;
              p++;
            }
        }
    }
  else
    {
      stash->adjusted_section_count = -1;
    }

  if (orig_bfd != stash->f.bfd_ptr)
    {
      set_debug_vma (orig_bfd, stash->f.bfd_ptr);
    }

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
    {
      return false;
    }

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    {
      return false;
    }

  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  for (struct info_list_node *node = lookup_info_hash_table (hash_table, name);
       node;
       node = node->next)
    {
      struct funcinfo *each_func = (struct funcinfo *) node->info;
      if (!each_func)
        {
          continue;
        }

      for (struct arange *arange = &each_func->arange;
           arange;
           arange = arange->next)
        {
          if (addr >= arange->low && addr < arange->high)
            {
              bfd_vma current_len = arange->high - arange->low;
              if (current_len < best_fit_len)
                {
                  best_fit = each_func;
                  best_fit_len = current_len;
                }
            }
        }
    }

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
  if (!hash_table || !sym || !filename_ptr || !linenumber_ptr)
    {
      return false;
    }

  const char *name = bfd_asymbol_name (sym);
  if (!name)
    {
      return false;
    }

  for (struct info_list_node *node = lookup_info_hash_table (hash_table, name);
       node != NULL;
       node = node->next)
    {
      if (node->info)
	{
	  struct varinfo *each = (struct varinfo *) node->info;
	  if (each->addr == addr)
	    {
	      *filename_ptr = each->file;
	      *linenumber_ptr = each->line;
	      return true;
	    }
	}
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
  struct comp_unit *start_unit;

  if (stash->f.all_comp_units == stash->hash_units_head)
    return true;

  start_unit = stash->hash_units_head
    ? stash->hash_units_head->prev_unit
    : stash->f.last_comp_unit;

  for (each = start_unit; each; each = each->prev_unit)
    {
      if (!comp_unit_hash_info (stash, each, stash->funcinfo_hash_table,
                                stash->varinfo_hash_table))
        {
          stash->info_hash_status = STASH_INFO_HASH_DISABLED;
          return false;
        }
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

  /* FIXME: Maybe we should check the reduce_memory_overheads
     and optimize fields in the bfd_link_info structure ?  */

  stash->funcinfo_hash_table = create_info_hash_table (abfd);
  stash->varinfo_hash_table = create_info_hash_table (abfd);

  if (stash->funcinfo_hash_table
      && stash->varinfo_hash_table
      && stash_maybe_update_info_hash_tables (stash))
    {
      stash->info_hash_status = STASH_INFO_HASH_ON;
    }
  else
    {
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
    }
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
  if (!stash || !sym || !filename_ptr || !linenumber_ptr)
    {
      return false;
    }

  BFD_ASSERT (stash->info_hash_status == STASH_INFO_HASH_ON);

  if ((sym->flags & BSF_FUNCTION) != 0)
    {
      return info_hash_lookup_funcinfo (stash->funcinfo_hash_table, sym, addr,
				      filename_ptr, linenumber_ptr);
    }

  return info_hash_lookup_varinfo (stash->varinfo_hash_table, sym, addr,
				   filename_ptr, linenumber_ptr);
}

/* Save current section VMAs.  */

static bool
save_section_vma (const bfd *abfd, struct dwarf2_debug *stash)
{
  bfd_vma *vmas;
  asection *s;
  unsigned int i;

  if (abfd->section_count == 0)
    {
      stash->sec_vma = NULL;
      stash->sec_vma_count = 0;
      return true;
    }

  vmas = bfd_calloc (abfd->section_count, sizeof (*vmas));
  if (vmas == NULL)
    return false;

  s = abfd->sections;
  for (i = 0; i < abfd->section_count; i++)
    {
      if (s == NULL)
        {
          bfd_free (vmas);
          return false;
        }

      if (s->output_section)
        vmas[i] = s->output_section->vma + s->output_offset;
      else
        vmas[i] = s->vma;
      
      s = s->next;
    }

  stash->sec_vma = vmas;
  stash->sec_vma_count = abfd->section_count;

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

  if (abfd->section_count != stash->sec_vma_count)
    {
      return false;
    }

  for (i = 0, s = abfd->sections;
       s != NULL && i < abfd->section_count;
       i++, s = s->next)
    {
      const bfd_vma vma = (s->output_section != NULL)
        ? (s->output_section->vma + s->output_offset)
        : s->vma;

      if (vma != stash->sec_vma[i])
        {
          return false;
        }
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
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;

  if (stash != NULL)
    {
      if (stash->orig_bfd_id == abfd->id
	  && section_vma_same (abfd, stash))
	{
	  if (stash->f.dwarf_info_size != 0)
	    return !do_place || place_sections (abfd, stash);
	  return false;
	}
      _bfd_dwarf2_cleanup_debug_info (abfd, pinfo);
    }

  stash = (struct dwarf2_debug *) bfd_zalloc (abfd, sizeof (*stash));
  if (!stash)
    return false;
  *pinfo = stash;

  stash->orig_bfd_id = abfd->id;
  stash->debug_sections = debug_sections;
  stash->f.syms = symbols;

  if (!save_section_vma (abfd, stash)
      || !(stash->f.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev, del_abbrev, calloc, free))
      || !(stash->alt.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev, del_abbrev, calloc, free))
      || !(stash->f.trie_root = alloc_trie_leaf (abfd))
      || !(stash->alt.trie_root = alloc_trie_leaf (abfd)))
    {
      _bfd_dwarf2_cleanup_debug_info (abfd, pinfo);
      return false;
    }

  bfd *local_debug_bfd = (debug_bfd != NULL) ? debug_bfd : abfd;
  asection *msec = find_debug_info (local_debug_bfd, debug_sections, NULL);

  if (msec == NULL && debug_bfd == NULL)
    {
      char *debug_filename = bfd_follow_build_id_debuglink (abfd, DEBUGDIR);
      if (debug_filename == NULL)
	debug_filename = bfd_follow_gnu_debuglink (abfd, DEBUGDIR);

      if (debug_filename != NULL)
	{
	  bfd *new_bfd = bfd_openr (debug_filename, NULL);
	  free (debug_filename);

	  if (new_bfd != NULL)
	    {
	      new_bfd->flags |= BFD_DECOMPRESS;
	      if (bfd_check_format (new_bfd, bfd_object)
		  && (msec = find_debug_info (new_bfd, debug_sections, NULL)) != NULL
		  && bfd_generic_link_read_symbols (new_bfd))
		{
		  local_debug_bfd = new_bfd;
		  stash->f.syms = bfd_get_outsymbols (local_debug_bfd);
		  stash->close_on_cleanup = true;
		}
	      else
		{
		  bfd_close (new_bfd);
		}
	    }
	}
    }

  if (msec == NULL)
    return false;

  stash->f.bfd_ptr = local_debug_bfd;

  if (do_place && !place_sections (abfd, stash))
    return false;

  bfd_size_type total_size;
  if (!find_debug_info (local_debug_bfd, debug_sections, msec))
    {
      total_size = bfd_get_section_limit_octets (local_debug_bfd, msec);
      if (!read_section (local_debug_bfd, &debug_sections[debug_info],
			 stash->f.syms, 0,
			 &stash->f.dwarf_info_buffer, &total_size))
	{
	  unset_sections (stash);
	  return false;
	}
    }
  else
    {
      total_size = 0;
      for (asection *sec = msec; sec; sec = find_debug_info (local_debug_bfd, debug_sections, sec))
	{
	  if (bfd_section_size_insane (local_debug_bfd, sec))
	    {
	      unset_sections (stash);
	      return false;
	    }
	  bfd_size_type readsz = bfd_get_section_limit_octets (local_debug_bfd, sec);
	  if (total_size + readsz < total_size)
	    {
	      bfd_set_error (bfd_error_no_memory);
	      unset_sections (stash);
	      return false;
	    }
	  total_size += readsz;
	}

      if (total_size > 0)
        {
          stash->f.dwarf_info_buffer = (bfd_byte *) bfd_malloc (total_size);
          if (stash->f.dwarf_info_buffer == NULL)
            {
              unset_sections (stash);
              return false;
            }
        }
      else
        stash->f.dwarf_info_buffer = NULL;

      bfd_size_type offset = 0;
      for (asection *sec = msec; sec; sec = find_debug_info (local_debug_bfd, debug_sections, sec))
	{
	  bfd_size_type readsz = bfd_get_section_limit_octets (local_debug_bfd, sec);
	  if (readsz == 0)
	    continue;
	  if (!bfd_simple_get_relocated_section_contents
	      (local_debug_bfd, sec, stash->f.dwarf_info_buffer + offset,
	       stash->f.syms))
	    {
	      unset_sections (stash);
	      return false;
	    }
	  offset += readsz;
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
  bfd_byte * const info_ptr_unit = file->info_ptr;
  bfd_byte * const info_ptr_end = file->dwarf_info_buffer + file->dwarf_info_size;

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

  struct comp_unit *each = parse_comp_unit (stash, file, file->info_ptr,
                                            length, info_ptr_unit, offset_size);
  if (!each)
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

  struct addr_range *r = (struct addr_range *) bfd_malloc (sizeof (struct addr_range));
  if (r == NULL)
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  r->start = each->info_ptr_unit;
  r->end = each->end_ptr;
  splay_tree_node v = splay_tree_lookup (file->comp_unit_tree, (splay_tree_key) r);

  if (v != NULL || r->end <= r->start)
    {
      free (r);
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  splay_tree_insert (file->comp_unit_tree, (splay_tree_key) r, (splay_tree_value) each);

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
  const asymbol *asym = (const asymbol *) sym;

  if (asym == NULL || asym->name == NULL)
    {
      return 0;
    }

  return htab_hash_string (asym->name);
}

/* Equality function for asymbols.  */

static int
eq_asymbol (const void *a, const void *b)
{
  const asymbol *sa;
  const asymbol *sb;

  if (a == b)
    {
      return 1;
    }

  if (a == NULL || b == NULL)
    {
      return 0;
    }

  sa = (const asymbol *) a;
  sb = (const asymbol *) b;

  if (sa->name == sb->name)
    {
      return 1;
    }

  if (sa->name == NULL || sb->name == NULL)
    {
      return 0;
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
  struct comp_unit *unit;
  htab_t sym_hash;
  bfd_signed_vma result = 0;
  asymbol **psym;
  int found = 0;

  stash = (struct dwarf2_debug *) *pinfo;

  if (stash == NULL || symbols == NULL)
    return 0;

  sym_hash = htab_create_alloc (10, hash_asymbol, eq_asymbol,
				NULL, xcalloc, free);

  for (psym = symbols; *psym != NULL; psym++)
    {
      asymbol *sym = *psym;

      if ((sym->flags & BSF_FUNCTION) && sym->section != NULL)
	{
	  void **slot = htab_find_slot (sym_hash, sym, INSERT);
	  if (slot != NULL)
	    {
	      *slot = sym;
	    }
	}
    }

  for (unit = stash->f.all_comp_units; unit != NULL && !found;
       unit = unit->next_unit)
    {
      struct funcinfo *func;

      comp_unit_maybe_decode_line_info (unit);

      for (func = unit->function_table; func != NULL; func = func->prev_func)
	{
	  if (func->name && func->arange.low)
	    {
	      asymbol search;
	      asymbol *sym;

	      search.name = func->name;
	      sym = htab_find (sym_hash, &search);
	      if (sym != NULL)
		{
		  result = func->arange.low - (sym->value + sym->section->vma);
		  found = 1;
		  break;
		}
	    }
	}
    }

  htab_delete (sym_hash);
  return result;
}

/* See _bfd_dwarf2_find_nearest_line_with_alt.  */

int _bfd_dwarf2_find_nearest_line(bfd *abfd,
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
    return _bfd_dwarf2_find_nearest_line_with_alt(abfd, NULL, symbols, symbol,
                                                  section, offset, filename_ptr,
                                                  functionname_ptr, linenumber_ptr,
                                                  discriminator_ptr,
                                                  debug_sections, pinfo);
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

static bfd *
open_alt_bfd (const char *alt_filename)
{
  bfd *alt_bfd = bfd_openr (alt_filename, NULL);
  if (alt_bfd == NULL)
    return NULL;

  if (!bfd_check_format (alt_bfd, bfd_object))
    {
      bfd_set_error (bfd_error_wrong_format);
      bfd_close (alt_bfd);
      return NULL;
    }
  return alt_bfd;
}

static asymbol *
find_symbol_for_data_section (bfd *abfd, asymbol **symbols, asection *section, bfd_vma offset)
{
  asymbol *found_symbol = NULL;
  for (asymbol **tmp = symbols; *tmp != NULL; ++tmp)
    {
      if ((*tmp)->the_bfd == abfd
	  && (*tmp)->section == section
	  && (*tmp)->value == offset
	  && ((*tmp)->flags & BSF_SECTION_SYM) == 0)
	{
	  found_symbol = *tmp;
	  if ((found_symbol->flags & BSF_GLOBAL) != 0)
	    break;
	}
    }
  return found_symbol;
}

static int
find_nearest_line_in_stashed_units (struct dwarf2_debug *stash, bfd_vma addr,
				    const char **filename_ptr, struct funcinfo **function_ptr,
				    unsigned int *linenumber_ptr, unsigned int *discriminator_ptr)
{
  struct trie_node *trie = stash->f.trie_root;
  unsigned int bits = VMA_BITS - 8;
  struct comp_unit **prev_each;
  struct comp_unit *each;

  while (trie && trie->num_room_in_leaf == 0)
    {
      int ch = (addr >> bits) & 0xff;
      trie = ((struct trie_interior *) trie)->children[ch];
      bits -= 8;
    }

  if (trie)
    {
      const struct trie_leaf *leaf = (const struct trie_leaf *) trie;
      for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
	leaf->ranges[i].unit->mark = false;

      for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
	{
	  struct comp_unit *unit = leaf->ranges[i].unit;
	  if (unit->mark
	      || addr < leaf->ranges[i].low_pc
	      || addr >= leaf->ranges[i].high_pc)
	    continue;
	  unit->mark = true;

	  if (comp_unit_find_nearest_line (unit, addr, filename_ptr,
					   function_ptr, linenumber_ptr,
					   discriminator_ptr))
	    return true;
	}
    }

  prev_each = &stash->f.all_comp_units_without_ranges;
  for (each = *prev_each; each; each = each->next_unit_without_ranges)
    {
      if (each->arange.high != 0)
	{
	  *prev_each = each->next_unit_without_ranges;
	  continue;
	}

      if (comp_unit_find_nearest_line (each, addr, filename_ptr,
				       function_ptr, linenumber_ptr,
				       discriminator_ptr))
	return true;
      prev_each = &each->next_unit_without_ranges;
    }

  return false;
}

static int
finalize_line_info (int found, struct dwarf2_debug *stash, bfd *abfd,
		    asymbol **symbols, asection *section, bfd_vma offset,
		    const char **filename_ptr, const char **functionname_ptr,
		    struct funcinfo *function)
{
  if (!functionname_ptr)
    return found;

  if (function && function->is_linkage)
    {
      *functionname_ptr = function->name;
      if (!found)
	return 2;
    }
  else if (!*functionname_ptr || (function && !function->is_linkage))
    {
      asymbol *fun;
      asymbol **syms = symbols;
      asection *sec = section;
      _bfd_dwarf2_stash_syms (stash, abfd, &sec, &syms);
      fun = _bfd_elf_find_function (abfd, syms, sec, offset,
				    *filename_ptr ? NULL : filename_ptr,
				    functionname_ptr);
      if (!found && fun != NULL)
	found = 2;

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
  return found;
}

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
  bool search_by_symbol;
  int found;
  struct funcinfo *function = NULL;

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
  if (!stash->f.info_ptr)
    return false;

  if (stash->alt.bfd_ptr == NULL && alt_filename != NULL)
    {
      stash->alt.bfd_ptr = open_alt_bfd (alt_filename);
      if (stash->alt.bfd_ptr == NULL)
	return false;
    }

  search_by_symbol = (symbol != NULL);
  if (search_by_symbol)
    {
      BFD_ASSERT (section == NULL && offset == 0 && functionname_ptr == NULL);
      section = bfd_asymbol_section (symbol);
      addr = symbol->value;
    }
  else
    {
      BFD_ASSERT (section != NULL && functionname_ptr != NULL);
      addr = offset;
      if (symbols != NULL && (section->flags & SEC_CODE) == 0)
	{
	  asymbol *data_sym = find_symbol_for_data_section (abfd, symbols, section, offset);
	  if (data_sym)
	    {
	      symbol = data_sym;
	      search_by_symbol = true;
	    }
	}
    }

  if (section->output_section)
    addr += section->output_section->vma + section->output_offset;
  else
    addr += section->vma;

  stash->inliner_chain = NULL;
  found = false;

  if (search_by_symbol)
    {
      if (stash->info_hash_status == STASH_INFO_HASH_OFF)
	stash_maybe_enable_info_hash_tables (abfd, stash);
      if (stash->info_hash_status == STASH_INFO_HASH_ON)
	stash_maybe_update_info_hash_tables (stash);

      if (stash->info_hash_status == STASH_INFO_HASH_ON)
	found = stash_find_line_fast (stash, symbol, addr, filename_ptr, linenumber_ptr);

      if (!found)
	{
	  for (struct comp_unit *each = stash->f.all_comp_units; each; each = each->next_unit)
	    if ((symbol->flags & BSF_FUNCTION) == 0
		|| comp_unit_may_contain_address (each, addr))
	      {
		if (comp_unit_find_line (each, symbol, addr, filename_ptr, linenumber_ptr))
		  {
		    found = true;
		    break;
		  }
	      }
	}
    }
  else
    {
      found = find_nearest_line_in_stashed_units (stash, addr, filename_ptr, &function,
						  linenumber_ptr, discriminator_ptr);
    }

  if (!found)
    {
      struct comp_unit *each;
      while ((each = stash_comp_unit (stash, &stash->f)) != NULL)
	{
	  if (search_by_symbol)
	    found = (((symbol->flags & BSF_FUNCTION) == 0
		      || comp_unit_may_contain_address (each, addr))
		     && comp_unit_find_line (each, symbol, addr,
					     filename_ptr, linenumber_ptr));
	  else
	    found = (comp_unit_may_contain_address (each, addr)
		     && comp_unit_find_nearest_line (each, addr,
						     filename_ptr,
						     &function,
						     linenumber_ptr,
						     discriminator_ptr));
	  if (found)
	    break;
	}
    }

  found = finalize_line_info (found, stash, abfd, symbols, section, offset,
			      filename_ptr, functionname_ptr, function);
  unset_sections (stash);
  return found;
}

bool
_bfd_dwarf2_find_inliner_info (bfd *abfd ATTRIBUTE_UNUSED,
			       const char **filename_ptr,
			       const char **functionname_ptr,
			       unsigned int *linenumber_ptr,
			       void **pinfo)
{
  if (!pinfo || !*pinfo)
    {
      return false;
    }

  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;
  struct funcinfo *func = stash->inliner_chain;

  if (func && func->caller_func)
    {
      *filename_ptr = func->caller_file;
      *functionname_ptr = func->caller_func->name;
      *linenumber_ptr = func->caller_line;
      stash->inliner_chain = func->caller_func;
      return true;
    }

  return false;
}

static void
cleanup_comp_unit (struct comp_unit *unit,
		   const struct line_info_table *parent_line_table)
{
  struct funcinfo *func;
  struct varinfo *var;

  if (unit->line_table && unit->line_table != parent_line_table)
    {
      free (unit->line_table->files);
      free (unit->line_table->dirs);
    }

  free (unit->lookup_funcinfo_table);
  unit->lookup_funcinfo_table = NULL;

  for (func = unit->function_table; func; func = func->prev_func)
    {
      free (func->file);
      func->file = NULL;
      free (func->caller_file);
      func->caller_file = NULL;
    }

  for (var = unit->variable_table; var; var = var->prev_var)
    {
      free (var->file);
      var->file = NULL;
    }
}

static void
cleanup_dwarf2_file (struct dwarf2_debug_file *file)
{
  struct comp_unit *unit;

  for (unit = file->all_comp_units; unit; unit = unit->next_unit)
    {
      cleanup_comp_unit (unit, file->line_table);
    }

  if (file->line_table)
    {
      free (file->line_table->files);
      free (file->line_table->dirs);
    }

  htab_delete (file->abbrev_offsets);
  if (file->comp_unit_tree != NULL)
    {
      splay_tree_delete (file->comp_unit_tree);
    }

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

void
_bfd_dwarf2_cleanup_debug_info (bfd *abfd, void **pinfo)
{
  struct dwarf2_debug *stash;

  if (abfd == NULL || pinfo == NULL || *pinfo == NULL)
    {
      return;
    }

  stash = (struct dwarf2_debug *) *pinfo;

  if (stash->varinfo_hash_table)
    {
      bfd_hash_table_free (&stash->varinfo_hash_table->base);
    }
  if (stash->funcinfo_hash_table)
    {
      bfd_hash_table_free (&stash->funcinfo_hash_table->base);
    }

  cleanup_dwarf2_file (&stash->f);
  cleanup_dwarf2_file (&stash->alt);

  free (stash->sec_vma);
  free (stash->adjusted_sections);

  if (stash->close_on_cleanup)
    {
      bfd_close (stash->f.bfd_ptr);
    }
  if (stash->alt.bfd_ptr)
    {
      bfd_close (stash->alt.bfd_ptr);
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
better_fit (elf_find_function_cache *  cache,
	    asymbol *                  sym,
	    bfd_vma                    code_off,
	    bfd_size_type              code_size,
	    bfd_vma                    offset)
{
  if (code_off > offset)
    return false;

  if (code_off > cache->code_off)
    return true;

  if (code_off < cache->code_off)
    return false;

  bool cache_covers_offset = (cache->code_off + cache->code_size > offset);
  bool sym_covers_offset = (code_off + code_size > offset);

  if (sym_covers_offset != cache_covers_offset)
    return sym_covers_offset;

  if (!cache_covers_offset)
    return code_size > cache->code_size;

  bool cache_is_func = (cache->func->flags & BSF_FUNCTION) != 0;
  bool sym_is_func = (sym->flags & BSF_FUNCTION) != 0;

  if (sym_is_func != cache_is_func)
    return sym_is_func;

  const elf_symbol_type *cache_elf_sym = (const elf_symbol_type *) cache->func;
  const elf_symbol_type *sym_elf_sym = (const elf_symbol_type *) sym;

  int cache_type = ELF_ST_TYPE (cache_elf_sym->internal_elf_sym.st_info);
  int sym_type = ELF_ST_TYPE (sym_elf_sym->internal_elf_sym.st_info);
  
  bool cache_is_typed = (cache_type != STT_NOTYPE);
  bool sym_is_typed = (sym_type != STT_NOTYPE);

  if (sym_is_typed != cache_is_typed)
    return sym_is_typed;

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
  if (symbols == NULL || bfd_get_flavour (abfd) != bfd_target_elf_flavour)
    return NULL;

  elf_find_function_cache *cache = elf_tdata (abfd)->elf_find_function_cache;
  if (cache == NULL)
    {
      cache = bfd_zalloc (abfd, sizeof (*cache));
      if (cache == NULL)
	return NULL;
      elf_tdata (abfd)->elf_find_function_cache = cache;
    }

  bool is_cache_hit = (cache->last_section == section
		       && cache->func != NULL
		       && offset >= cache->code_off
		       && offset < cache->code_off + cache->code_size);

  if (!is_cache_hit)
    {
      asymbol *last_file_sym = NULL;
      enum {
	STATE_NOTHING_SEEN,
	STATE_SYMBOL_SEEN,
	STATE_FILE_AFTER_SYMBOL_SEEN
      } search_state = STATE_NOTHING_SEEN;
      const struct elf_backend_data *bed = get_elf_backend_data (abfd);

      cache->last_section = section;
      cache->func = NULL;
      cache->filename = NULL;
      cache->code_size = 0;
      cache->code_off = 0;

      for (asymbol **p = symbols; *p != NULL; p++)
	{
	  asymbol *sym = *p;

	  if ((sym->flags & BSF_FILE) != 0)
	    {
	      last_file_sym = sym;
	      if (search_state == STATE_SYMBOL_SEEN)
		search_state = STATE_FILE_AFTER_SYMBOL_SEEN;
	      continue;
	    }

	  if (search_state == STATE_NOTHING_SEEN)
	    search_state = STATE_SYMBOL_SEEN;

	  bfd_vma sym_code_off;
	  bfd_size_type sym_size = bed->maybe_function_sym (sym, section, &sym_code_off);

	  if (sym_size == 0)
	    continue;

	  if (better_fit (cache, sym, sym_code_off, sym_size, offset))
	    {
	      cache->func = sym;
	      cache->code_size = sym_size;
	      cache->code_off = sym_code_off;

	      bool use_filename = (last_file_sym != NULL
				   && ((sym->flags & BSF_LOCAL) != 0
				       || search_state != STATE_FILE_AFTER_SYMBOL_SEEN));
	      cache->filename = use_filename ? bfd_asymbol_name (last_file_sym) : NULL;
	    }
	  else if (cache->func != NULL
		   && sym_code_off > offset
		   && sym_code_off > cache->code_off
		   && sym_code_off < cache->code_off + cache->code_size)
	    {
	      cache->code_size = sym_code_off - cache->code_off;
	    }
	}
    }

  if (cache->func == NULL)
    return NULL;

  if (filename_ptr != NULL)
    *filename_ptr = cache->filename;
  if (functionname_ptr != NULL)
    *functionname_ptr = bfd_asymbol_name (cache->func);

  return cache->func;
}
