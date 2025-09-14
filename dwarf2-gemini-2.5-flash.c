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
  size_t base_size = sizeof(struct trie_leaf);
  size_t element_count = TRIE_LEAF_SIZE;
  size_t element_size = sizeof(((struct trie_leaf *)0)->ranges[0]);

  if (element_count > 0 && element_size > SIZE_MAX / element_count) {
    return NULL;
  }
  size_t array_part_size = element_count * element_size;

  if (base_size > SIZE_MAX - array_part_size) {
    return NULL;
  }
  size_t total_allocation_size = base_size + array_part_size;

  leaf = bfd_zalloc (abfd, total_allocation_size);
  if (leaf == NULL) {
    return NULL;
  }

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
  bool r1_contains_r2_start = (r1->start <= r2->start && r2->start < r1->end);

  // The expression (r2->end - 1) computes the last address in r2.
  // For unsigned integer types, if r2->end is 0, this expression wraps around
  // to the maximum value of the type. The subsequent comparisons correctly
  // handle this by effectively making the clause false. This behavior is
  // explicitly preserved to maintain original functionality.
  bool r1_contains_r2_last_addr = (r1->start <= (r2->end - 1) && (r2->end - 1) < r1->end);

  return r1_contains_r2_start || r1_contains_r2_last_addr;
}

/* Compare function for splay tree of addr_ranges.  */

static int
splay_tree_compare_addr_range (splay_tree_key xa, splay_tree_key xb)
{
  const struct addr_range *r1 = (const struct addr_range *) xa;
  const struct addr_range *r2 = (const struct addr_range *) xb;

  if (addr_range_intersects (r1, r2))
    return 0;
  else if (r1->end <= r2->start)
    return -1;
  else
    return 1;
}

/* Splay tree release function for keys (addr_range).  */

static void
splay_tree_free_addr_range (splay_tree_key key)
{
  free(key);
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
  struct info_hash_entry *info_entry_allocated;
  struct info_hash_entry *result_entry;

  if (entry == NULL)
    {
      info_entry_allocated = (struct info_hash_entry *) bfd_hash_allocate (table, sizeof (struct info_hash_entry));
      if (info_entry_allocated == NULL)
	return NULL;
    }
  else
    {
      info_entry_allocated = (struct info_hash_entry *) entry;
    }

  result_entry = (struct info_hash_entry *)
                 bfd_hash_newfunc ((struct bfd_hash_entry *) info_entry_allocated, table, string);

  if (result_entry != NULL)
    {
      result_entry->head = NULL;
    }

  return (struct bfd_hash_entry *) result_entry;
}

/* Function to create a new info hash table.  It returns a pointer to the
   newly created table or NULL if there is any error.  We need abfd
   solely for memory allocation.  */

static struct info_hash_table *
create_info_hash_table (bfd *abfd)
{
  struct info_hash_table *hash_table;

  hash_table = bfd_alloc (abfd, sizeof (struct info_hash_table));
  if (!hash_table)
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
insert_info_hash_table (struct info_hash_table *hash_table,
			const char *key,
			void *info,
			bool copy_p)
{
  struct info_hash_entry *entry = (struct info_hash_entry *)
    bfd_hash_lookup (&hash_table->base, key, true, copy_p);
  if (!entry)
    {
      return false;
    }

  struct info_list_node *node = (struct info_list_node *)
    bfd_hash_allocate (&hash_table->base, sizeof (*node));
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
  const struct info_hash_entry *entry;

  entry = (struct info_hash_entry*) bfd_hash_lookup (&hash_table->base, key,
						     false, false);
  return entry ? entry->head : NULL;
}

/* Read a section into its appropriate place in the dwarf2_debug
   struct (indicated by SECTION_BUFFER and SECTION_SIZE).  If SYMS is
   not NULL, use bfd_simple_get_relocated_section_contents to read the
   section contents, otherwise use bfd_get_section_contents.  Fail if
   the located section does not contain at least OFFSET bytes.  */

static bool
validate_offset_and_return_status (uint64_t offset, bfd_size_type section_size,
                                   const char *section_name_for_error)
{
  if (offset != 0 && offset >= section_size)
    {
      _bfd_error_handler (_("DWARF error: offset (%" PRIu64 ")"
                            " greater than or equal to %s size (%" PRIu64 ")"),
                          (uint64_t) offset, section_name_for_error,
                          (uint64_t) section_size);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
read_section (bfd *abfd,
              const struct dwarf_debug_section *sec,
              asymbol **syms,
              uint64_t offset,
              bfd_byte **section_buffer,
              bfd_size_type *section_size)
{
  bfd_byte *contents = *section_buffer;
  const char *section_name = NULL;
  asection *msec = NULL;
  bfd_size_type current_section_data_size = 0;
  bool allocated_here = false;

  if (contents != NULL)
    {
      if (!validate_offset_and_return_status(offset, *section_size, sec->uncompressed_name))
        {
          return false;
        }
      return true;
    }

  msec = bfd_get_section_by_name (abfd, sec->uncompressed_name);
  if (msec != NULL)
    {
      section_name = sec->uncompressed_name;
    }
  else
    {
      msec = bfd_get_section_by_name (abfd, sec->compressed_name);
      if (msec != NULL)
        {
          section_name = sec->compressed_name;
        }
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

  current_section_data_size = bfd_get_section_limit_octets (abfd, msec);

  if (current_section_data_size == BFD_SIZE_TYPE_MAX)
    {
      _bfd_error_handler (_("DWARF error: section %s size is too large to safely NUL-terminate."),
                          section_name);
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  bfd_size_type alloc_size = current_section_data_size + 1;
  contents = (bfd_byte *) bfd_malloc (alloc_size);
  if (contents == NULL)
    {
      return false;
    }
  allocated_here = true;

  bool read_success;
  if (syms)
    {
      read_success = bfd_simple_get_relocated_section_contents (abfd, msec, contents, syms);
    }
  else
    {
      read_success = bfd_get_section_contents (abfd, msec, contents, 0, current_section_data_size);
    }

  if (!read_success)
    {
      goto cleanup_fail;
    }

  contents[current_section_data_size] = 0;

  if (!validate_offset_and_return_status(offset, current_section_data_size, section_name))
    {
      goto cleanup_fail;
    }

  *section_buffer = contents;
  *section_size = current_section_data_size;
  return true;

cleanup_fail:
  if (allocated_here && contents != NULL)
    {
      free (contents);
    }
  *section_buffer = NULL;
  return false;
}

/* Read dwarf information from a buffer.  */

static inline uint64_t
read_n_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end, int n)
{
  bfd_byte *current_pos = *ptr;
  if (end - current_pos < n)
    {
      *ptr = end;
      return 0;
    }
  *ptr = current_pos + n;
  return bfd_get (n * 8, abfd, current_pos);
}

static inline unsigned int
read_1_byte (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 1);
}

static int
read_1_signed_byte (bfd *abfd ATTRIBUTE_UNUSED, bfd_byte **ptr, bfd_byte *end)
{
  bfd_byte *read_from_ptr = *ptr;

  if (read_from_ptr >= end)
    {
      *ptr = end;
      return 0;
    }

  *ptr = read_from_ptr + 1;
  return bfd_get_signed_8 (abfd, read_from_ptr);
}

static unsigned int
read_2_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  const int bytes_to_read = 2;
  return read_n_bytes (abfd, ptr, end, bytes_to_read);
}

static unsigned int
read_3_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  unsigned int byte1 = read_1_byte (abfd, ptr, end);
  unsigned int byte2 = read_1_byte (abfd, ptr, end);
  unsigned int byte3 = read_1_byte (abfd, ptr, end);
  unsigned int val;

  if (bfd_little_endian (abfd))
    {
      val = byte1 | (byte2 << 8) | (byte3 << 16);
    }
  else
    {
      val = (byte1 << 16) | (byte2 << 8) | byte3;
    }
  return val;
}

static inline unsigned int
read_4_bytes (const bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, 4);
}

static uint64_t
read_8_bytes (const bfd *abfd, bfd_byte **ptr, const bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, (uint64_t) 8);
}

#include <stddef.h>

static struct dwarf_block *
read_blk (bfd *abfd, bfd_byte **ptr, bfd_byte *end, size_t size)
{
  bfd_byte *buf = *ptr;
  struct dwarf_block *block;
  ptrdiff_t diff_available;
  size_t available_bytes;

  block = bfd_alloc (abfd, sizeof (*block));
  if (block == NULL)
    {
      return NULL;
    }

  if (buf > end)
    {
      diff_available = 0;
    }
  else
    {
      diff_available = end - buf;
    }

  available_bytes = (size_t) diff_available;

  if (size > available_bytes)
    {
      block->data = NULL;
      block->size = 0;
      *ptr = end;
    }
  else
    {
      block->data = buf;
      block->size = size;
      *ptr = buf + size;
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
  bfd_byte *current_pos = *ptr;
  bfd_byte *string_start = current_pos;

  while (current_pos < buf_end)
    {
      if (*current_pos == 0)
        {
          // A null terminator was found.
          // Now, check if this null terminator was at the very beginning
          // of where we started looking for a string (`string_start`).
          // The original function's behavior for a string starting with '\0'
          // was to return NULL, not an empty string. This behavior is preserved.
          if (string_start == current_pos)
            {
              // The "string" started and ended with a null byte at the same location.
              // Advance the buffer pointer past this null byte.
              *ptr = current_pos + 1;
              return NULL; // Return NULL as per original functionality.
            }
          else
            {
              // A valid non-empty string was found.
              // Advance the buffer pointer past the null terminator.
              *ptr = current_pos + 1;
              return (char *) string_start;
            }
        }
      // Move to the next byte if the current one is not a null terminator.
      current_pos++;
    }

  // If the loop completes, it means no null terminator was found
  // within the specified buffer range.
  // Update the buffer pointer to the end of the buffer.
  *ptr = current_pos; // This will be equal to buf_end.
  return NULL; // No complete string found.
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
  uint64_t offset_val;
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  char *result_str;

  if (unit->offset_size > (size_t)(buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  if (unit->offset_size == 4)
    {
      offset_val = read_4_bytes (unit->abfd, ptr, buf_end);
    }
  else if (unit->offset_size == 8)
    {
      offset_val = read_8_bytes (unit->abfd, ptr, buf_end);
    }
  else
    {
      return NULL;
    }

  if (!read_section (unit->abfd, &stash->debug_sections[debug_str],
                      file->syms, offset_val,
                      &file->dwarf_str_buffer, &file->dwarf_str_size))
    {
      return NULL;
    }

  if (offset_val >= file->dwarf_str_size)
    {
      return NULL;
    }

  result_str = (char *)(file->dwarf_str_buffer + offset_val);

  if (*result_str == '\0')
    {
      return NULL;
    }

  return result_str;
}

/* Like read_indirect_string but from .debug_line_str section.  */

static char *
read_indirect_line_string (struct comp_unit *unit,
			   bfd_byte **ptr,
			   bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
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

  if (! read_section (unit->abfd, &stash->debug_sections[debug_line_str],
		      file->syms, offset,
		      &file->dwarf_line_str_buffer,
		      &file->dwarf_line_str_size))
    return NULL;

  if (offset >= file->dwarf_line_str_size)
    {
      return NULL;
    }

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
  char *str_ptr;

  if (unit->offset_size > (size_t) (buf_end - *ptr))
    {
      *ptr = buf_end;
      return NULL;
    }

  if (unit->offset_size == 4)
    {
      offset = read_4_bytes (unit->abfd, ptr, buf_end);
    }
  else
    {
      offset = read_8_bytes (unit->abfd, ptr, buf_end);
    }

  if (stash->alt.bfd_ptr == NULL)
    {
      bfd *debug_bfd = NULL;
      char *debug_filename = NULL;

      debug_filename = bfd_follow_gnu_debugaltlink (unit->abfd, DEBUGDIR);
      if (debug_filename == NULL)
        {
          return NULL;
        }

      debug_bfd = bfd_openr (debug_filename, NULL);
      free (debug_filename);
      if (debug_bfd == NULL)
        {
          return NULL;
        }

      if (!bfd_check_format (debug_bfd, bfd_object))
        {
          bfd_close (debug_bfd);
          return NULL;
        }
      stash->alt.bfd_ptr = debug_bfd;
    }

  if (! read_section (stash->alt.bfd_ptr,
		      stash->debug_sections + debug_str_alt,
		      stash->alt.syms, offset,
		      &stash->alt.dwarf_str_buffer,
		      &stash->alt.dwarf_str_size))
    {
      return NULL;
    }

  str_ptr = (char *) stash->alt.dwarf_str_buffer + offset;
  if (*str_ptr == '\0')
    {
      return NULL;
    }

  return str_ptr;
}

/* Resolve an alternate reference from UNIT at OFFSET.
   Returns a pointer into the loaded alternate CU upon success
   or NULL upon failure.  */

static bfd *
initialize_alt_debug_bfd(struct comp_unit *unit, struct dwarf2_debug *stash)
{
  char *debug_filename = bfd_follow_gnu_debugaltlink(unit->abfd, DEBUGDIR);
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

  stash->alt.bfd_ptr = debug_bfd;
  return debug_bfd;
}

static bfd_byte *
read_alt_indirect_ref (struct comp_unit *unit, uint64_t offset)
{
  struct dwarf2_debug *stash = unit->stash;
  bfd *alt_bfd = stash->alt.bfd_ptr;

  if (alt_bfd == NULL)
    {
      alt_bfd = initialize_alt_debug_bfd(unit, stash);
      if (alt_bfd == NULL)
        return NULL;
    }

  if (!read_section(alt_bfd,
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
  bfd_byte *buf = *ptr;
  int signed_vma = 0;
  uint64_t result_val = 0;

  if (bfd_get_flavour (unit->abfd) == bfd_target_elf_flavour)
    {
      signed_vma = get_elf_backend_data (unit->abfd)->sign_extend_vma;
    }

  if (unit->addr_size > (size_t) (buf_end - buf))
    {
      *ptr = buf_end;
      return 0;
    }

  *ptr = buf + unit->addr_size;

  switch (unit->addr_size)
    {
    case 8:
      if (signed_vma)
        {
          result_val = bfd_get_signed_64 (unit->abfd, buf);
        }
      else
        {
          result_val = bfd_get_64 (unit->abfd, buf);
        }
      break;
    case 4:
      if (signed_vma)
        {
          result_val = (uint64_t) bfd_get_signed_32 (unit->abfd, buf);
        }
      else
        {
          result_val = (uint64_t) bfd_get_32 (unit->abfd, buf);
        }
      break;
    case 2:
      if (signed_vma)
        {
          result_val = (uint64_t) bfd_get_signed_16 (unit->abfd, buf);
        }
      else
        {
          result_val = (uint64_t) bfd_get_16 (unit->abfd, buf);
        }
      break;
    default:
      abort ();
    }

  return result_val;
}

/* Lookup an abbrev_info structure in the abbrev hash table.  */

static struct abbrev_info *
lookup_abbrev (unsigned int number, struct abbrev_info **abbrevs)
{
  unsigned int hash_index;
  const struct abbrev_info *current_abbrev;

  hash_index = number % ABBREV_HASH_SIZE;
  current_abbrev = abbrevs[hash_index];

  while (current_abbrev != NULL)
    {
      if (current_abbrev->number == number)
	return (struct abbrev_info *)current_abbrev;
      else
	current_abbrev = current_abbrev->next;
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
  const struct abbrev_offset_entry *ent = (const struct abbrev_offset_entry *)p;
  return htab_hash_pointer ((void *) ent->offset);
}

static int
eq_abbrev (const void *pa, const void *pb)
{
  const struct abbrev_offset_entry *a = (const struct abbrev_offset_entry *)pa;
  const struct abbrev_offset_entry *b = (const struct abbrev_offset_entry *)pb;
  return a->offset == b->offset;
}

#include <stdlib.h>

struct abbrev_info {
  void *attrs;
  struct abbrev_info *next;
};

struct abbrev_offset_entry {
  struct abbrev_info **abbrevs;
};

#ifndef ABBREV_HASH_SIZE
#define ABBREV_HASH_SIZE 1024
#endif

static void
del_abbrev (void *p)
{
  if (p == NULL)
    {
      return;
    }

  struct abbrev_offset_entry *ent = (struct abbrev_offset_entry *)p;

  if (ent->abbrevs != NULL)
    {
      for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
        {
          struct abbrev_info *current = ent->abbrevs[i];
          struct abbrev_info *temp_to_free;

          while (current != NULL)
            {
              temp_to_free = current;
              current = current->next;

              free (temp_to_free->attrs);
              free (temp_to_free);
            }
          ent->abbrevs[i] = NULL;
        }

      free(ent->abbrevs);
      ent->abbrevs = NULL;
    }

  free (ent);
}

/* In DWARF version 2, the description of the debugging information is
   stored in a separate .debug_abbrev section.  Before we read any
   dies from a section we read in all abbreviations and install them
   in a hash table.  */

static void
free_abbrev_list_data (struct abbrev_info **abbrevs_ht)
{
  if (abbrevs_ht == NULL)
    return;

  for (size_t i = 0; i < ABBREV_HASH_SIZE; i++)
    {
      struct abbrev_info *abbrev = abbrevs_ht[i];
      while (abbrev)
	{
	  struct abbrev_info *next_abbrev = abbrev->next;
	  free (abbrev->attrs);
	  free (abbrev);
	  abbrev = next_abbrev;
	}
    }
  free (abbrevs_ht);
}

static struct abbrev_info**
read_abbrevs (bfd *abfd, uint64_t offset, struct dwarf2_debug *stash,
	      struct dwarf2_debug_file *file)
{
  struct abbrev_info **abbrevs = NULL;
  bfd_byte *abbrev_ptr;
  bfd_byte *abbrev_end;
  struct abbrev_info *cur_abbrev = NULL;
  unsigned int abbrev_number;
  void **slot;
  struct abbrev_offset_entry temp_key = { offset, NULL };

  slot = htab_find_slot (file->abbrev_offsets, &temp_key, INSERT);
  if (slot == NULL)
    return NULL;
  if (*slot != NULL)
    return ((struct abbrev_offset_entry *) (*slot))->abbrevs;

  if (! read_section (abfd, &stash->debug_sections[debug_abbrev],
		      file->syms, offset,
		      &file->dwarf_abbrev_buffer,
		      &file->dwarf_abbrev_size))
    return NULL;

  if (offset > file->dwarf_abbrev_size)
    return NULL;

  size_t hash_table_alloc_size = sizeof (struct abbrev_info*) * ABBREV_HASH_SIZE;
  abbrevs = (struct abbrev_info **) bfd_zalloc (abfd, hash_table_alloc_size);
  if (abbrevs == NULL)
    return NULL;

  abbrev_ptr = file->dwarf_abbrev_buffer + offset;
  abbrev_end = file->dwarf_abbrev_buffer + file->dwarf_abbrev_size;

  abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);

  while (abbrev_number)
    {
      cur_abbrev = (struct abbrev_info *) bfd_zalloc (abfd, sizeof (struct abbrev_info));
      if (cur_abbrev == NULL)
	goto fail;

      cur_abbrev->number = abbrev_number;
      cur_abbrev->tag = (enum dwarf_tag)
	_bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
      cur_abbrev->has_children = read_1_byte (abfd, &abbrev_ptr, abbrev_end);

      for (;;)
	{
	  unsigned int abbrev_name;
	  unsigned int abbrev_form;
	  bfd_vma implicit_const_val = (bfd_vma) -1;

	  abbrev_name = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
	  abbrev_form = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);

	  if (abbrev_name == 0)
	    break;

	  if (abbrev_form == DW_FORM_implicit_const)
	    implicit_const_val = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, true, abbrev_end);

	  if ((cur_abbrev->num_attrs % ATTR_ALLOC_CHUNK) == 0)
	    {
	      struct attr_abbrev *tmp;
	      size_t new_attrs_count = cur_abbrev->num_attrs + ATTR_ALLOC_CHUNK;
	      size_t new_attrs_size = new_attrs_count * sizeof (struct attr_abbrev);
	      tmp = (struct attr_abbrev *) bfd_realloc (cur_abbrev->attrs, new_attrs_size);
	      if (tmp == NULL)
		goto fail;
	      cur_abbrev->attrs = tmp;
	    }

	  cur_abbrev->attrs[cur_abbrev->num_attrs].name = (enum dwarf_attribute) abbrev_name;
	  cur_abbrev->attrs[cur_abbrev->num_attrs].form = (enum dwarf_form) abbrev_form;
	  cur_abbrev->attrs[cur_abbrev->num_attrs].implicit_const = implicit_const_val;
	  ++cur_abbrev->num_attrs;
	}

      unsigned int hash_number = abbrev_number % ABBREV_HASH_SIZE;
      cur_abbrev->next = abbrevs[hash_number];
      abbrevs[hash_number] = cur_abbrev;
      cur_abbrev = NULL;

      if ((size_t) (abbrev_ptr - file->dwarf_abbrev_buffer) >= file->dwarf_abbrev_size)
	break;

      abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);

      if (abbrev_number != 0 && lookup_abbrev (abbrev_number, abbrevs) != NULL)
	break;
    }

  struct abbrev_offset_entry *new_entry = bfd_malloc (sizeof *new_entry);
  if (new_entry == NULL)
    goto fail;
  
  new_entry->offset = offset;
  new_entry->abbrevs = abbrevs;
  *slot = new_entry;
  
  return abbrevs;

fail:
  free_abbrev_list_data(abbrevs);
  if (cur_abbrev != NULL)
    {
      free(cur_abbrev->attrs);
      free(cur_abbrev);
    }
  return NULL;
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
  if (attr == NULL)
    {
      return false;
    }

  switch (attr->form)
    {
    case DW_FORM_addr:
    case DW_FORM_addrx:
    case DW_FORM_addrx1:
    case DW_FORM_addrx2:
    case DW_FORM_addrx3:
    case DW_FORM_addrx4:
    case DW_FORM_data1:
    case DW_FORM_data2:
    case DW_FORM_data4:
    case DW_FORM_data8:
    case DW_FORM_flag:
    case DW_FORM_flag_present:
    case DW_FORM_GNU_ref_alt:
    case DW_FORM_implicit_const:
    case DW_FORM_ref1:
    case DW_FORM_ref2:
    case DW_FORM_ref4:
    case DW_FORM_ref8:
    case DW_FORM_ref_addr:
    case DW_FORM_ref_sig8:
    case DW_FORM_ref_udata:
    case DW_FORM_sdata:
    case DW_FORM_sec_offset:
    case DW_FORM_udata:
      return true;

    default:
      return false;
    }
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
  bfd_byte *info_ptr;
  size_t offset_idx_mult_size;
  size_t final_offset;

  if (!read_section (unit->abfd, &stash->debug_sections[debug_addr],
		     file->syms, 0,
		     &file->dwarf_addr_buffer, &file->dwarf_addr_size))
    return 0;

  if (unit->addr_size != 4 && unit->addr_size != 8)
    return 0;

  if (file->dwarf_addr_size < unit->addr_size)
    return 0;

  if (_bfd_mul_overflow (idx, unit->addr_size, &offset_idx_mult_size))
    return 0;

  if (_bfd_add_overflow (offset_idx_mult_size, unit->dwarf_addr_offset, &final_offset))
    return 0;

  if (final_offset > file->dwarf_addr_size - unit->addr_size)
    return 0;

  info_ptr = file->dwarf_addr_buffer + final_offset;

  if (unit->addr_size == 4)
    return bfd_get_32 (unit->abfd, info_ptr);
  else
    return bfd_get_64 (unit->abfd, info_ptr);
}

/* Returns the string using DW_AT_str_offsets_base.
   Used to implement DW_FORM_strx*.  */
static const char *
read_indexed_string (uint64_t idx, struct comp_unit *unit)
{
  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  bfd_byte *info_ptr;
  uint64_t str_offset_val;
  size_t offset_product;
  size_t current_offset;

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

  if (_bfd_mul_overflow (idx, unit->offset_size, &offset_product))
    return NULL;

  current_offset = offset_product + unit->dwarf_str_offset;
  if (current_offset < offset_product) /* Unsigned addition overflow check */
    return NULL;

  if (current_offset >= file->dwarf_str_offsets_size
      || unit->offset_size > file->dwarf_str_offsets_size - current_offset)
    return NULL;

  info_ptr = file->dwarf_str_offsets_buffer + current_offset;

  if (unit->offset_size == 4)
    str_offset_val = bfd_get_32 (unit->abfd, info_ptr);
  else if (unit->offset_size == 8)
    str_offset_val = bfd_get_64 (unit->abfd, info_ptr);
  else
    return NULL;

  if (str_offset_val >= file->dwarf_str_size)
    return NULL;

  return (const char *) file->dwarf_str_buffer + str_offset_val;
}

/* Read and fill in the value of attribute ATTR as described by FORM.
   Read data starting from INFO_PTR, but never at or beyond INFO_PTR_END.
   Returns an updated INFO_PTR taking into account the amount of data read.  */

static bfd_vma
dwarf_read_fixed_size_value(bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end, unsigned int size)
{
  switch (size)
    {
    case 1: return read_1_byte(abfd, info_ptr, info_ptr_end);
    case 2: return read_2_bytes(abfd, info_ptr, info_ptr_end);
    case 3: return read_3_bytes(abfd, info_ptr, info_ptr_end);
    case 4: return read_4_bytes(abfd, info_ptr, info_ptr_end);
    case 8: return read_8_bytes(abfd, info_ptr, info_ptr_end);
    default:
      _bfd_error_handler(_("DWARF error: unsupported value size for fixed-size form: %u"), size);
      bfd_set_error(bfd_error_bad_value);
      return 0;
    }
}

static bfd_vma
dwarf_get_indexed_address(bfd_vma index_val, struct comp_unit *unit)
{
  if (unit->dwarf_addr_offset != 0)
    return read_indexed_address(index_val, unit);
  return index_val;
}

static const char *
dwarf_get_indexed_string(bfd_vma index_val, struct comp_unit *unit)
{
  if (unit->dwarf_str_offset != 0)
    return (const char *) read_indexed_string(index_val, unit);
  return NULL;
}

static bfd_byte *
dwarf_read_block_data(bfd *abfd, bfd_byte **info_ptr, bfd_byte *info_ptr_end, size_t amt)
{
  bfd_byte *blk = read_blk(abfd, info_ptr, info_ptr_end, amt);
  return blk;
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

    case DW_FORM_ref_addr:
      if (unit->version >= 3)
	{
	  attr->u.val = dwarf_read_fixed_size_value(abfd, &info_ptr, info_ptr_end, unit->offset_size);
	}
      else
	{
	  attr->u.val = read_address(unit, &info_ptr, info_ptr_end);
	}
      break;

    case DW_FORM_addr:
      attr->u.val = read_address(unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_GNU_ref_alt:
    case DW_FORM_sec_offset:
      attr->u.val = dwarf_read_fixed_size_value(abfd, &info_ptr, info_ptr_end, unit->offset_size);
      break;

    case DW_FORM_block2:
      amt = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.blk = dwarf_read_block_data(abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;

    case DW_FORM_block4:
      amt = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.blk = dwarf_read_block_data(abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;

    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      attr->u.val = read_1_byte(abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx1:
      attr->u.val = read_1_byte(abfd, &info_ptr, info_ptr_end);
      attr->u.val = dwarf_get_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_data2:
    case DW_FORM_ref2:
      attr->u.val = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx2:
      attr->u.val = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.val = dwarf_get_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_addrx3:
      attr->u.val = read_3_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.val = dwarf_get_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_ref4:
    case DW_FORM_data4:
      attr->u.val = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx4:
      attr->u.val = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.val = dwarf_get_indexed_address(attr->u.val, unit);
      break;

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
      attr->u.val = read_1_byte(abfd, &info_ptr, info_ptr_end);
      attr->u.str = dwarf_get_indexed_string(attr->u.val, unit);
      break;

    case DW_FORM_strx2:
      attr->u.val = read_2_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.str = dwarf_get_indexed_string(attr->u.val, unit);
      break;

    case DW_FORM_strx3:
      attr->u.val = read_3_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.str = dwarf_get_indexed_string(attr->u.val, unit);
      break;

    case DW_FORM_strx4:
      attr->u.val = read_4_bytes(abfd, &info_ptr, info_ptr_end);
      attr->u.str = dwarf_get_indexed_string(attr->u.val, unit);
      break;

    case DW_FORM_strx:
      attr->u.val = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      attr->u.str = dwarf_get_indexed_string(attr->u.val, unit);
      break;

    case DW_FORM_exprloc:
    case DW_FORM_block:
      amt = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      attr->u.blk = dwarf_read_block_data(abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;

    case DW_FORM_block1:
      amt = read_1_byte(abfd, &info_ptr, info_ptr_end);
      attr->u.blk = dwarf_read_block_data(abfd, &info_ptr, info_ptr_end, amt);
      if (attr->u.blk == NULL)
	return NULL;
      break;

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
      attr->u.val = dwarf_get_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_indirect:
      form = _bfd_safe_read_leb128(abfd, &info_ptr, false, info_ptr_end);
      if (form == DW_FORM_implicit_const)
	implicit_const = _bfd_safe_read_leb128(abfd, &info_ptr, true, info_ptr_end);
      info_ptr = read_attribute_value(attr, form, implicit_const, unit,
				       info_ptr, info_ptr_end);
      break;

    case DW_FORM_implicit_const:
      attr->form = DW_FORM_sdata;
      attr->u.sval = implicit_const;
      break;

    case DW_FORM_data16:
      attr->u.blk = dwarf_read_block_data(abfd, &info_ptr, info_ptr_end, 16);
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
  if (attr == NULL || abbrev == NULL || unit == NULL)
    return NULL;

  if (info_ptr == NULL || info_ptr > info_ptr_end)
    return NULL;

  attr->name = abbrev->name;

  info_ptr = read_attribute_value (attr,
                                   abbrev->form,
                                   abbrev->implicit_const,
                                   unit,
                                   info_ptr,
                                   info_ptr_end);

  if (info_ptr == NULL)
    return NULL;

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
new_line_sorts_after (const struct line_info *new_line, const struct line_info *line)
{
  if (new_line->address > line->address)
    {
      return true;
    }
  else if (new_line->address < line->address)
    {
      return false;
    }
  else /* new_line->address == line->address */
    {
      return new_line->op_index > line->op_index;
    }
}


/* Adds a new entry to the line_info list in the line_info_table, ensuring
   that the list is sorted.  Note that the line_info list is sorted from
   highest to lowest VMA (with possible duplicates); that is,
   line_info->prev_line always accesses an equal or smaller VMA.  */

```c
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
  struct line_info* info = NULL;
  bool ret_status = false; /* Assume failure, set to true on success path. */

  /* Allocate memory for the new line_info structure. */
  info = (struct line_info *) bfd_alloc (table->abfd, sizeof (struct line_info));
  if (info == NULL)
    goto cleanup;

  /* Initialize all fields of the new line_info structure to safe defaults. */
  info->prev_line = NULL;
  info->address = address;
  info->op_index = op_index;
  info->line = line;
  info->column = column;
  info->discriminator = discriminator;
  info->end_sequence = end_sequence;
  info->filename = NULL; /* Initialize to NULL, will be set if a filename is provided. */

  /* Handle filename duplication if a valid filename string is provided. */
  if (filename != NULL && *filename != '\0')
    {
      size_t filename_len = strlen (filename);
      info->filename = (char *) bfd_alloc (table->abfd, filename_len + 1);
      if (info->filename == NULL)
	goto cleanup; /* Error: filename allocation failed, free 'info' and return. */
      memcpy (info->filename, filename, filename_len + 1); /* Use memcpy for robustness. */
    }

  /* Determine the correct location for 'info' within the line_info_table's sequences. */
  struct line_sequence *current_seq = table->sequences;

  if (current_seq != NULL
      && current_seq->last_line->address == address
      && current_seq->last_line->op_index == op_index
      && current_seq->last_line->end_sequence == end_sequence)
    {
      /* Case 1: Duplicate entry.
         We only keep the last entry with the same address and end sequence (PR ld/4986).
         Replace the existing 'last_line' with the new 'info'. */
      struct line_info *old_last_line = current_seq->last_line;

      /* If 'lcl_head' pointed to the old 'last_line', it must be updated to point to 'info'. */
      if (table->lcl_head == old_last_line)
	table->lcl_head = info;

      info->prev_line = old_last_line->prev_line;
      current_seq->last_line = info;

      /* Free the old line_info structure and its associated filename to prevent memory leaks. */
      if (old_last_line->filename != NULL)
	bfd_free (table->abfd, old_last_line->filename);
      bfd_free (table->abfd, old_last_line);
      ret_status = true;
    }
  else if (current_seq == NULL || current_seq->last_line->end_sequence)
    {
      /* Case 2: Start a new line sequence.
         This occurs if there are no existing sequences or the last sequence has ended. */
      struct line_sequence* new_seq = (struct line_sequence *) bfd_malloc (sizeof (struct line_sequence));
      if (new_seq == NULL)
	goto cleanup; /* Error: new sequence allocation failed, free 'info' and its filename. */

      new_seq->low_pc = address;
      new_seq->prev_sequence = table->sequences; /* Link the new sequence to the previous one. */
      new_seq->last_line = info;
      table->lcl_head = info; /* The head of the new sequence is also the 'lcl_head'. */
      table->sequences = new_seq; /* Update the table's current/latest sequence. */
      table->num_sequences++;
      ret_status = true;
    }
  else if (info->end_sequence
	   || new_line_sorts_after (info, current_seq->last_line))
    {
      /* Case 3: Normal addition.
         Add 'info' to the beginning (head) of the current sequence.
         This applies if 'info' ends a sequence or sorts after the current 'last_line'. */
      info->prev_line = current_seq->last_line;
      current_seq->last_line = info;

      /* Initialize 'lcl_head' if it's currently NULL. */
      if (table->lcl_head == NULL)
	table->lcl_head = info;
      ret_status = true;
    }
  else if (!new_line_sorts_after (info, table->lcl_head)
	   && (table->lcl_head->prev_line == NULL
	       || new_line_sorts_after (info, table->lcl_head->prev_line)))
    {
      /* Case 4: Abnormal but easy insertion.
         'lcl_head' is the correct insertion point for 'info'.
         'info' sorts before 'lcl_head' but after 'lcl_head->prev_line'. */
      info->prev_line = table->lcl_head->prev_line;
      table->lcl_head->prev_line = info;
      ret_status = true;
    }
  else
    {
      /* Case 5: Abnormal and hard insertion.
         Neither 'last_line' nor 'lcl_head' are valid heads for 'info'.
         Perform a linear scan through the current sequence to find the correct insertion point. */
      struct line_info* li2 = current_seq->last_line; /* 'li2' is always non-NULL at this point. */
      struct line_info* li1 = li2->prev_line;

      while (li1 != NULL)
	{
	  if (!new_line_sorts_after (info, li2)
	      && new_line_sorts_after (info, li1))
	    break; /* Found the insertion point: 'info' goes between 'li1' and 'li2'. */

	  li2 = li1; /* Move 'li2' to 'li1'. */
	  li1 = li1->prev_line; /* Move 'li1' further down the list. */
	}
      
      table->lcl_head = li2; /* Update 'lcl_head' to the newly found insertion point ('li2'). */
      info->prev_line = table->lcl_head->prev_line;
      table->lcl_head->prev_line = info;

      /* Update the 'low_pc' of the current sequence if the new address is lower. */
      if (address < current_seq->low_pc)
	current_seq->low_pc = address;
      ret_status = true;
    }

cleanup:
  /* If an error occurred (ret_status is false), then 'info' (and its filename)
     was allocated but not successfully inserted into the table. It must be freed. */
  if (!ret_status && info != NULL)
    {
      if (info->filename != NULL)
	bfd_free (table->abfd, info->filename);
      bfd_free (table->abfd, info);
    }
  return ret_status;
}
```

/* Extract a fully qualified filename from a line info table.
   The returned string has been malloc'ed and it is the caller's
   responsibility to free it.  */

static char *
alloc_unknown_string (void)
{
  char *s = strdup ("<unknown>");
  if (s == NULL)
    _bfd_error_handler (_("DWARF error: Out of memory allocating <unknown> string."));
  return s;
}

static char *
concat_filename (struct line_info_table *table, unsigned int file)
{
  if (table == NULL)
    {
      _bfd_error_handler (_("DWARF error: mangled line number section (NULL table)"));
      return alloc_unknown_string ();
    }

  if (!table->use_dir_and_file_0)
    {
      if (file == 0)
	return alloc_unknown_string ();
      file--;
    }

  if (file >= table->num_files)
    {
      _bfd_error_handler (_("DWARF error: mangled line number section (bad file number)"));
      return alloc_unknown_string ();
    }

  char *filename = table->files[file].name;
  if (filename == NULL)
    return alloc_unknown_string ();

  if (IS_ABSOLUTE_PATH (filename))
    {
      char *abs_filename_copy = strdup (filename);
      if (abs_filename_copy == NULL)
        _bfd_error_handler (_("DWARF error: Out of memory copying absolute filename."));
      return abs_filename_copy;
    }

  char *base_dir = NULL;
  char *intermediate_dir = NULL;
  unsigned int dir_idx = table->files[file].dir;

  if (!table->use_dir_and_file_0)
    dir_idx--;

  char *raw_subdir = NULL;
  if (dir_idx < table->num_dirs)
    raw_subdir = table->dirs[dir_idx];

  if (raw_subdir == NULL || !IS_ABSOLUTE_PATH (raw_subdir))
    {
      base_dir = table->comp_dir;
      if (raw_subdir != NULL)
	intermediate_dir = raw_subdir;
    }
  else
    {
      base_dir = raw_subdir;
      intermediate_dir = NULL;
    }

  if (base_dir == NULL && intermediate_dir != NULL)
    {
      base_dir = intermediate_dir;
      intermediate_dir = NULL;
    }

  if (base_dir == NULL)
    {
      char *filename_copy = strdup (filename);
      if (filename_copy == NULL)
        _bfd_error_handler (_("DWARF error: Out of memory copying filename without base dir."));
      return filename_copy;
    }

  size_t len = strlen (base_dir) + strlen (filename) + 2;
  if (intermediate_dir != NULL)
    len += strlen (intermediate_dir) + 1;

  char *name = (char *) bfd_malloc (len);
  if (name == NULL)
    {
      _bfd_error_handler (_("DWARF error: Out of memory concatenating filename."));
      return NULL;
    }

  int result;
  if (intermediate_dir != NULL)
    result = snprintf (name, len, "%s/%s/%s", base_dir, intermediate_dir, filename);
  else
    result = snprintf (name, len, "%s/%s", base_dir, filename);

  if (result < 0 || (size_t)result >= len)
    {
      _bfd_error_handler (_("DWARF error: snprintf failed or truncated filename."));
      bfd_free (name);
      return NULL;
    }

  return name;
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
alloc_trie_leaf (bfd *abfd); // Forward declaration

static bool
ranges_overlap (bfd_vma low1, bfd_vma high1, bfd_vma low2, bfd_vma high2)
{
  /* Ranges are [low, high), meaning low is inclusive, high is exclusive.
     They overlap if low1 < high2 AND low2 < high1.  */
  return low1 < high2 && low2 < high1;
}

static bool
try_merge_arange_in_leaf(struct trie_leaf *leaf, struct comp_unit *unit,
                         bfd_vma low_pc, bfd_vma high_pc)
{
  unsigned int i;
  for (i = 0; i < leaf->num_stored_in_leaf; ++i)
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
          return true;
        }
    }
  return false;
}

static void
add_range_to_leaf(struct trie_leaf *leaf, struct comp_unit *unit,
                  bfd_vma low_pc, bfd_vma high_pc)
{
  unsigned int i = leaf->num_stored_in_leaf++;
  leaf->ranges[i].unit = unit;
  leaf->ranges[i].low_pc = low_pc;
  leaf->ranges[i].high_pc = high_pc;
}

static struct trie_node *
insert_arange_in_trie (bfd *abfd,
                       struct trie_node *trie,
                       bfd_vma trie_pc,
                       unsigned int trie_pc_bits,
                       struct comp_unit *unit,
                       bfd_vma low_pc,
                       bfd_vma high_pc);

static struct trie_node *
handle_leaf_node(bfd *abfd, struct trie_node *trie_node_ptr,
                 bfd_vma trie_pc, unsigned int trie_pc_bits,
                 struct comp_unit *unit, bfd_vma low_pc, bfd_vma high_pc)
{
  struct trie_leaf *leaf = (struct trie_leaf *)trie_node_ptr;

  /* 1. Attempt to merge with an existing range in this leaf. */
  if (try_merge_arange_in_leaf(leaf, unit, low_pc, high_pc))
    {
      return trie_node_ptr;
    }

  /* 2. If there's room, add the new range directly. */
  if (leaf->num_stored_in_leaf < leaf->head.num_room_in_leaf)
    {
      add_range_to_leaf(leaf, unit, low_pc, high_pc);
      return trie_node_ptr;
    }

  /* Leaf is full. Decide whether to split into an interior node or expand leaf capacity. */

  bool splitting_will_help = false;
  if (trie_pc_bits < VMA_BITS)
    {
      /* Calculate the inclusive highest address for the current trie bucket. */
      bfd_vma bucket_max_addr = trie_pc | (((bfd_vma)-1) >> trie_pc_bits);

      /* Splitting helps if at least one stored range does not cover the entire bucket.
         (i.e., it starts after trie_pc OR ends before bucket_max_addr + 1). */
      for (unsigned int i = 0; i < leaf->num_stored_in_leaf; ++i)
        {
          if (leaf->ranges[i].low_pc > trie_pc
              || leaf->ranges[i].high_pc <= bucket_max_addr) /* high_pc is exclusive */
            {
              splitting_will_help = true;
              break;
            }
        }
    }

  if (splitting_will_help)
    {
      /* Convert the leaf node to an interior node. */
      struct trie_interior *new_interior = bfd_zalloc(abfd, sizeof(struct trie_interior));
      if (!new_interior)
        return NULL;

      struct trie_node *result_node = (struct trie_node*)new_interior;
      const struct trie_leaf *old_leaf = leaf; /* Keep pointer to original data */

      /* Re-insert all ranges from the old leaf into the new interior node. */
      for (unsigned int i = 0; i < old_leaf->num_stored_in_leaf; ++i)
        {
          result_node = insert_arange_in_trie(abfd, result_node, trie_pc, trie_pc_bits,
                                              old_leaf->ranges[i].unit,
                                              old_leaf->ranges[i].low_pc,
                                              old_leaf->ranges[i].high_pc);
          if (!result_node)
            return NULL; /* Propagate allocation failure */
        }

      /* Finally, insert the new range. */
      result_node = insert_arange_in_trie(abfd, result_node, trie_pc, trie_pc_bits,
                                          unit, low_pc, high_pc);
      if (!result_node)
        return NULL;

      /* Note: The old `leaf` node's memory is now orphaned.
         If `bfd_zalloc` uses an arena or the `abfd` context manages memory
         lifetime, this might be implicitly handled. If `bfd_zalloc` is a simple
         `malloc` wrapper, this will cause a memory leak. Given the constraint
         "without altering its external functionality", direct `free` calls
         or changes to the function signature to enable caller-side freeing
         are not permitted. We assume `abfd`'s memory management handles this. */

      return result_node;
    }
  else
    {
      /* Leaf is full, and splitting won't help (or we're at max depth).
         Expand the leaf's capacity. */
      unsigned int new_room_in_leaf = leaf->head.num_room_in_leaf * 2;
      /* Check for integer overflow when doubling capacity, or if initial capacity was zero. */
      if (new_room_in_leaf == 0 || new_room_in_leaf < leaf->head.num_room_in_leaf)
        {
          /* Overflow detected or unable to expand further.
             Returning NULL indicates an unrecoverable error for this path. */
          return NULL;
        }

      size_t amt = sizeof(struct trie_leaf) + new_room_in_leaf * sizeof(leaf->ranges[0]);
      struct trie_leaf *new_leaf = bfd_zalloc(abfd, amt);
      if (!new_leaf)
        return NULL;

      new_leaf->head.num_room_in_leaf = new_room_in_leaf;
      new_leaf->num_stored_in_leaf = leaf->num_stored_in_leaf;
      memcpy(new_leaf->ranges, leaf->ranges,
             leaf->num_stored_in_leaf * sizeof(leaf->ranges[0]));

      /* Insert the new range into the expanded leaf. */
      add_range_to_leaf(new_leaf, unit, low_pc, high_pc);

      /* See note above regarding memory management of the old `leaf`. */
      return &new_leaf->head;
    }
}

static struct triie_node *
handle_interior_node(bfd *abfd, struct trie_node *trie_node_ptr,
                     bfd_vma trie_pc, unsigned int trie_pc_bits,
                     struct comp_unit *unit, bfd_vma low_pc, bfd_vma high_pc)
{
  struct trie_interior *interior = (struct trie_interior *)trie_node_ptr;

  /* Clamp the range to the current trie bucket's boundaries. */
  bfd_vma clamped_low_pc = low_pc;
  bfd_vma clamped_high_pc = high_pc;

  if (trie_pc_bits < VMA_BITS)
    {
      bfd_vma bucket_max_addr = trie_pc | (((bfd_vma)-1) >> trie_pc_bits);
      if (clamped_low_pc < trie_pc)
        clamped_low_pc = trie_pc;
      /* high_pc is exclusive, bucket_max_addr is inclusive.
         If clamped_high_pc covers beyond bucket_max_addr, trim it. */
      if (clamped_high_pc > bucket_max_addr + 1)
        clamped_high_pc = bucket_max_addr + 1;
    }

  /* If the range becomes empty or inverted after clamping, there's nothing to insert.
     Ranges are [low, high), so low >= high implies an empty range. */
  if (clamped_low_pc >= clamped_high_pc)
    {
      return trie_node_ptr;
    }

  /* Determine the child buckets affected by the clamped range.
     The next 8 bits (one byte) determine the child index. */
  unsigned int shift_amount = VMA_BITS - (trie_pc_bits + 8);
  int from_ch = (clamped_low_pc >> shift_amount) & 0xff;
  /* (clamped_high_pc - 1) gets the last address within the clamped range. */
  int to_ch = ((clamped_high_pc - 1) >> shift_amount) & 0xff;

  for (int ch = from_ch; ch <= to_ch; ++ch)
    {
      struct trie_node *child = interior->children[ch];

      if (child == NULL)
        {
          child = alloc_trie_leaf(abfd);
          if (!child)
            return NULL;
        }

      /* Calculate the `trie_pc` for the child bucket. */
      bfd_vma child_trie_pc_offset = (bfd_vma)ch << shift_amount;
      bfd_vma child_trie_pc = trie_pc + child_trie_pc_offset;

      /* Recursively insert the original range (not clamped) into the child.
         The clamping is specific to the current level's `trie_pc` and `trie_pc_bits`,
         but the full range needs to be propagated down to allow full coverage
         of sub-buckets that are entirely within the range. */
      child = insert_arange_in_trie(abfd, child,
                                    child_trie_pc,
                                    trie_pc_bits + 8,
                                    unit, low_pc, high_pc);
      if (!child)
        return NULL;

      interior->children[ch] = child;
    }

  return trie_node_ptr;
}

static struct trie_node *
insert_arange_in_trie (bfd *abfd,
                       struct trie_node *trie,
                       bfd_vma trie_pc,
                       unsigned int trie_pc_bits,
                       struct comp_unit *unit,
                       bfd_vma low_pc,
                       bfd_vma high_pc)
{
  /* If the input range is invalid (empty), do nothing.
     Ranges are [low, high), so low >= high implies an empty range. */
  if (low_pc >= high_pc)
    {
      return trie;
    }

  /* If the trie is NULL (e.g., initial call for an empty trie), create a root leaf. */
  if (trie == NULL)
    {
      trie = alloc_trie_leaf(abfd);
      if (!trie)
        return NULL;
    }

  if (trie->num_room_in_leaf > 0)
    {
      /* The current node is a leaf. */
      return handle_leaf_node(abfd, trie, trie_pc, trie_pc_bits,
                              unit, low_pc, high_pc);
    }
  else
    {
      /* The current node is an interior node. */
      return handle_interior_node(abfd, trie, trie_pc, trie_pc_bits,
                                  unit, low_pc, high_pc);
    }
}

static bool
arange_add (struct comp_unit *unit, struct arange *first_arange,
	    struct trie_node **trie_root, bfd_vma low_pc, bfd_vma high_pc)
{
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

  for (struct arange *current_arange = first_arange; current_arange != NULL; current_arange = current_arange->next)
    {
      if (low_pc == current_arange->high)
	{
	  current_arange->high = high_pc;
	  return true;
	}
      if (high_pc == current_arange->low)
	{
	  current_arange->low = low_pc;
	  return true;
	}
    }

  struct arange *new_arange = bfd_alloc (unit->abfd, sizeof (*new_arange));
  if (new_arange == NULL)
    return false;

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
  const struct line_sequence* seq1 = (const struct line_sequence*)a;
  const struct line_sequence* seq2 = (const struct line_sequence*)b;
  int result;

  result = (seq1->low_pc > seq2->low_pc) - (seq1->low_pc < seq2->low_pc);
  if (result != 0) {
    return result;
  }

  result = (seq2->last_line->address > seq1->last_line->address) - (seq2->last_line->address < seq1->last_line->address);
  if (result != 0) {
    return result;
  }

  result = (seq2->last_line->op_index > seq1->last_line->op_index) - (seq2->last_line->op_index < seq1->last_line->op_index);
  if (result != 0) {
    return result;
  }

  result = (seq1->num_lines > seq2->num_lines) - (seq1->num_lines < seq2->num_lines);
  if (result != 0) {
    return result;
  }

  return 0;
}

/* Construct the line information table for quick lookup.  */

static bool
build_line_info_table (struct line_info_table *  table,
		       struct line_sequence *    seq)
{
  struct line_info **line_info_lookup;
  struct line_info *each_line;
  unsigned int num_lines = 0;
  unsigned int line_index;
  size_t allocation_size;

  if (seq->line_info_lookup != NULL)
    return true;

  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    num_lines++;

  seq->num_lines = num_lines;
  if (num_lines == 0)
    return true;

  allocation_size = num_lines * sizeof (struct line_info*);
  line_info_lookup = bfd_alloc (table->abfd, allocation_size);
  seq->line_info_lookup = line_info_lookup;

  if (line_info_lookup == NULL)
    return false;

  line_index = num_lines;
  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    line_info_lookup[--line_index] = each_line;

  BFD_ASSERT (line_index == 0);
  return true;
}

/* Sort the line sequences for quick lookup.  */

static bool
sort_line_sequences (struct line_info_table* table)
{
  size_t allocation_size;
  struct line_sequence *sequences_array;
  struct line_sequence *current_list_node;
  unsigned int i;
  unsigned int initial_num_sequences = table->num_sequences;
  unsigned int final_num_sequences;
  bfd_vma last_high_pc;

  if (initial_num_sequences == 0)
    {
      return true;
    }

  allocation_size = sizeof(struct line_sequence) * initial_num_sequences;
  sequences_array = (struct line_sequence *) bfd_alloc (table->abfd, allocation_size);
  if (sequences_array == NULL)
    {
      return false;
    }

  current_list_node = table->sequences;
  for (i = 0; i < initial_num_sequences; i++)
    {
      struct line_sequence* node_to_free = current_list_node;

      BFD_ASSERT (current_list_node);

      sequences_array[i].low_pc = current_list_node->low_pc;
      sequences_array[i].prev_sequence = NULL;
      sequences_array[i].last_line = current_list_node->last_line;
      sequences_array[i].line_info_lookup = NULL; /* As per original logic, reset for array structure */
      sequences_array[i].num_lines = current_list_node->num_lines; /* Preserve original value */

      current_list_node = current_list_node->prev_sequence;
      free (node_to_free);
    }
  BFD_ASSERT (current_list_node == NULL);

  qsort (sequences_array, initial_num_sequences, sizeof (struct line_sequence), compare_sequences);

  if (initial_num_sequences == 0)
    {
      table->sequences = NULL;
      table->num_sequences = 0;
      return true;
    }

  final_num_sequences = 0;
  last_high_pc = sequences_array[0].last_line->address;

  /* Always include the first sorted sequence. */
  sequences_array[final_num_sequences] = sequences_array[0];
  final_num_sequences++;

  for (i = 1; i < initial_num_sequences; i++)
    {
      struct line_sequence *current_seq_src = &sequences_array[i];

      if (current_seq_src->low_pc < last_high_pc)
	{
	  if (current_seq_src->last_line->address <= last_high_pc)
	    {
	      /* Skip nested entries. */
	      continue;
	    }
	  /* Trim overlapping entries. */
	  current_seq_src->low_pc = last_high_pc;
	}

      last_high_pc = current_seq_src->last_line->address;

      /* Copy the (potentially modified) source sequence to the next available slot. */
      sequences_array[final_num_sequences] = *current_seq_src;
      final_num_sequences++;
    }

  table->sequences = sequences_array;
  table->num_sequences = final_num_sequences;
  return true;
}

/* Add directory to TABLE.  CUR_DIR memory ownership is taken by TABLE.  */

static bool
line_info_add_include_dir (struct line_info_table *table, char *cur_dir)
{
  if (table->num_dirs % DIR_ALLOC_CHUNK == 0)
    {
      size_t new_capacity;
      size_t required_bytes;
      char **new_dirs;

      new_capacity = table->num_dirs + DIR_ALLOC_CHUNK;

      if (new_capacity > SIZE_MAX / sizeof (char *))
        {
          return false;
        }

      required_bytes = new_capacity * sizeof (char *);

      new_dirs = bfd_realloc (table->dirs, required_bytes);

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
				unsigned int dir,
				unsigned int xtime,
				unsigned int size)
{
  (void)dir;
  (void)xtime;
  (void)size;
  return line_info_add_include_dir (table, cur_dir);
}

/* Add file to TABLE.  CUR_FILE memory ownership is taken by TABLE.  */

static bool
line_info_add_file_name (struct line_info_table *table, char *cur_file,
			 unsigned int dir, unsigned int xtime,
			 unsigned int size)
{
  if (table == NULL)
    {
      return false;
    }

  // The condition (table->num_files % FILE_ALLOC_CHUNK) == 0 triggers reallocation.
  // This ensures that when table->num_files is 0, FILE_ALLOC_CHUNK, 2*FILE_ALLOC_CHUNK, etc.,
  // a reallocation attempt is made to expand capacity.
  if ((table->num_files % FILE_ALLOC_CHUNK) == 0)
    {
      struct fileinfo *tmp;
      size_t current_num_files_as_size_t = table->num_files;
      size_t new_capacity_elements;
      size_t new_total_size_bytes;

      // 1. Calculate the new total number of elements required for reallocation.
      // This will be the current count + FILE_ALLOC_CHUNK.
      // Check for addition overflow before performing the operation.
      // Assuming FILE_ALLOC_CHUNK is a positive value.
      if (current_num_files_as_size_t > (SIZE_MAX - (size_t)FILE_ALLOC_CHUNK))
        {
          // The addition would overflow size_t. This indicates a very large allocation request.
          return false;
        }
      new_capacity_elements = current_num_files_as_size_t + (size_t)FILE_ALLOC_CHUNK;

      // 2. Calculate the total size in bytes for the new allocation.
      // This is new_capacity_elements * sizeof(struct fileinfo).
      // Check for multiplication overflow.
      if (sizeof (struct fileinfo) == 0)
        {
          // Defensive check: elements must have a non-zero size.
          return false;
        }
      if (new_capacity_elements > (SIZE_MAX / sizeof (struct fileinfo)))
        {
          // The multiplication would overflow size_t.
          return false;
        }
      new_total_size_bytes = new_capacity_elements * sizeof (struct fileinfo);

      // Attempt to reallocate memory. bfd_realloc is assumed to behave like realloc.
      // If table->files is NULL, bfd_realloc acts like malloc.
      tmp = bfd_realloc (table->files, new_total_size_bytes);
      if (tmp == NULL)
	    {
	      // Memory reallocation failed.
	      return false;
	    }
      table->files = tmp;
    }

  // Assign the new file's information to the next available slot.
  // table->num_files acts as the current count and the next available index.
  table->files[table->num_files].name = cur_file;
  table->files[table->num_files].dir = dir;
  table->files[table->num_files].time = xtime;
  table->files[table->num_files].size = size;

  // Increment the count of files stored in the table.
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
  bfd_byte format_count;
  bfd_vma data_count;
  bfd_byte *buf = *bufp;
  bfd_byte *format_read_ptr;

  format_count = read_1_byte (abfd, &buf, buf_end);

  /* Define a structure for parsed format entries.
     Using a VLA is safe here as format_count is a bfd_byte (max 255),
     making the stack allocation size predictable and small. This avoids
     dynamic memory management overhead and potential leaks. */
  struct format_entry {
    bfd_vma content_type;
    bfd_vma form;
  } formats[format_count > 0 ? format_count : 1]; /* Avoid zero-sized VLA */

  format_read_ptr = buf;
  for (unsigned int formati = 0; formati < format_count; formati++)
    {
      formats[formati].content_type = _bfd_safe_read_leb128 (abfd, &format_read_ptr, false, buf_end);
      if (format_read_ptr == NULL)
	return false;
      formats[formati].form = _bfd_safe_read_leb128 (abfd, &format_read_ptr, false, buf_end);
      if (format_read_ptr == NULL)
	return false;
    }
  buf = format_read_ptr;

  data_count = _bfd_safe_read_leb128 (abfd, &buf, false, buf_end);
  if (buf == NULL)
    return false;

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

  for (bfd_vma datai = 0; datai < data_count; datai++)
    {
      struct fileinfo fe;
      memset (&fe, 0, sizeof fe);

      for (unsigned int formati = 0; formati < format_count; formati++)
	{
	  bfd_vma current_content_type = formats[formati].content_type;
	  bfd_vma current_form = formats[formati].form;

	  char **target_string_ptr = NULL;
	  unsigned int *target_uint_ptr = NULL;
	  bool discard_value = false;

	  switch (current_content_type)
	    {
	    case DW_LNCT_path:
	      target_string_ptr = &fe.name;
	      break;
	    case DW_LNCT_directory_index:
	      target_uint_ptr = &fe.dir;
	      break;
	    case DW_LNCT_timestamp:
	      target_uint_ptr = &fe.time;
	      break;
	    case DW_LNCT_size:
	      target_uint_ptr = &fe.size;
	      break;
	    case DW_LNCT_MD5:
	      discard_value = true;
	      break;
	    default:
	      _bfd_error_handler
		(_("DWARF error: unknown format content type %" PRIu64),
		 (uint64_t) current_content_type);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }

	  struct attribute attr;
	  buf = read_attribute_value (&attr, current_form, 0, unit, buf, buf_end);
	  if (buf == NULL)
	    return false;

	  if (!discard_value)
	    {
	      switch (current_form)
		{
		case DW_FORM_string:
		case DW_FORM_line_strp:
		case DW_FORM_strx:
		case DW_FORM_strx1:
		case DW_FORM_strx2:
		case DW_FORM_strx3:
		case DW_FORM_strx4:
		  if (target_string_ptr != NULL)
		    *target_string_ptr = attr.u.str;
		  break;

		case DW_FORM_data1:
		case DW_FORM_data2:
		case DW_FORM_data4:
		case DW_FORM_data8:
		case DW_FORM_udata:
		  if (target_uint_ptr != NULL)
		    *target_uint_ptr = attr.u.val;
		  break;

		case DW_FORM_data16:
		  /* MD5 data (attr.blk) or other block data is ignored if
		     not specifically mapped to a fileinfo field. This matches
		     the original behavior. */
		  break;
		}
	    }
	}

      if (!callback (table, fe.name, fe.dir, fe.time, fe.size))
	return false;
    }

  *bufp = buf;
  return true;
}

/* Decode the line number information for UNIT.  */

static bool bfd_dwarf2_read_line_info_prologue(bfd *abfd, bfd_byte **line_ptr_p,
                                               bfd_byte **line_end_p, struct line_head *lh,
                                               unsigned int unit_addr_size);
static bool bfd_dwarf2_read_line_tables(struct comp_unit *unit, bfd_byte **line_ptr_p,
                                        bfd_byte *line_end, struct line_info_table *table,
                                        unsigned int dwarf_version);
static bool bfd_dwarf2_process_line_sequence(struct comp_unit *unit, bfd_byte **line_ptr_p,
                                             bfd_byte *line_end, const struct line_head *lh,
                                             struct line_info_table *table);

static bool
bfd_dwarf2_read_line_info_prologue(bfd *abfd, bfd_byte **line_ptr_p,
                                   bfd_byte **line_end_p, struct line_head *lh,
                                   unsigned int unit_addr_size)
{
  bfd_byte *line_ptr = *line_ptr_p;
  bfd_byte *line_end = *line_end_p;
  unsigned int offset_size;

  if (line_ptr + 4 > line_end)
    {
      _bfd_error_handler(_("DWARF error: ran out of room reading total length"));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  lh->total_length = read_4_bytes(abfd, &line_ptr, line_end);
  offset_size = 4;

  if (lh->total_length == 0xffffffff)
    {
      if (line_ptr + 8 > line_end)
	{
	  _bfd_error_handler(_("DWARF error: ran out of room reading 64-bit total length"));
	  bfd_set_error(bfd_error_bad_value);
	  return false;
	}
      lh->total_length = read_8_bytes(abfd, &line_ptr, line_end);
      offset_size = 8;
    }
  else if (lh->total_length == 0 && unit_addr_size == 8)
    {
      /* Handle (non-standard) 64-bit DWARF2 formats.  */
      if (line_ptr + 4 > line_end)
	{
	  _bfd_error_handler(_("DWARF error: ran out of room reading 64-bit DWARF2 total length"));
	  bfd_set_error(bfd_error_bad_value);
	  return false;
	}
      lh->total_length = read_4_bytes(abfd, &line_ptr, line_end);
      offset_size = 8;
    }

  if (lh->total_length > (size_t) (line_end - line_ptr))
    {
      _bfd_error_handler
	(_("DWARF error: line info data is bigger (%#" PRIx64 ")"
	   " than the space remaining in the section (%#lx)"),
	 (uint64_t) lh->total_length, (unsigned long) (line_end - line_ptr));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  *line_end_p = line_ptr + lh->total_length;
  line_end = *line_end_p;

  if (line_ptr + 2 > line_end)
    {
      _bfd_error_handler(_("DWARF error: ran out of room reading version"));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  lh->version = read_2_bytes(abfd, &line_ptr, line_end);
  if (lh->version < 2 || lh->version > 5)
    {
      _bfd_error_handler
	(_("DWARF error: unhandled .debug_line version %d"), lh->version);
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  size_t required_bytes_for_fixed_prologue_fields;
  if (lh->version >= 5)
    required_bytes_for_fixed_prologue_fields = 1 + 1 + offset_size + 1 + 1 + 1 + 1 + 1 + 1;
  else if (lh->version >= 4)
    required_bytes_for_fixed_prologue_fields = offset_size + 1 + 1 + 1 + 1 + 1 + 1;
  else
    required_bytes_for_fixed_prologue_fields = offset_size + 1 + 1 + 1 + 1 + 1;

  if ((size_t)(line_end - line_ptr) < required_bytes_for_fixed_prologue_fields)
    {
      _bfd_error_handler(_("DWARF error: ran out of room reading prologue fixed fields"));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  if (lh->version >= 5)
    {
      unsigned int segment_selector_size;

      read_1_byte(abfd, &line_ptr, line_end); /* Skip address size.  */

      segment_selector_size = read_1_byte(abfd, &line_ptr, line_end);
      if (segment_selector_size != 0)
	{
	  _bfd_error_handler
	    (_("DWARF error: line info unsupported segment selector size %u"),
	     segment_selector_size);
	  bfd_set_error(bfd_error_bad_value);
	  return false;
	}
    }

  if (offset_size == 4)
    lh->prologue_length = read_4_bytes(abfd, &line_ptr, line_end);
  else
    lh->prologue_length = read_8_bytes(abfd, &line_ptr, line_end);

  lh->minimum_instruction_length = read_1_byte(abfd, &line_ptr, line_end);

  if (lh->version >= 4)
    lh->maximum_ops_per_insn = read_1_byte(abfd, &line_ptr, line_end);
  else
    lh->maximum_ops_per_insn = 1;

  if (lh->maximum_ops_per_insn == 0)
    {
      _bfd_error_handler
	(_("DWARF error: invalid maximum operations per instruction"));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  lh->default_is_stmt = read_1_byte(abfd, &line_ptr, line_end);
  lh->line_base = read_1_signed_byte(abfd, &line_ptr, line_end);
  lh->line_range = read_1_byte(abfd, &line_ptr, line_end);
  lh->opcode_base = read_1_byte(abfd, &line_ptr, line_end);

  if (lh->opcode_base > 0 && (size_t)(line_end - line_ptr) < (size_t)(lh->opcode_base - 1))
    {
      _bfd_error_handler(_("DWARF error: ran out of room reading opcode lengths"));
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

  if (lh->opcode_base > 0)
    {
      size_t amt = lh->opcode_base * sizeof(unsigned char);
      lh->standard_opcode_lengths = (unsigned char *) bfd_alloc(abfd, amt);
      if (lh->standard_opcode_lengths == NULL)
        return false;
      memset(lh->standard_opcode_lengths, 0, amt);
      lh->standard_opcode_lengths[0] = 1; /* DW_LNS_extended_op has length 0, but opcode_base is 1-indexed. */
    }
  else
    {
      lh->standard_opcode_lengths = NULL;
    }

  for (unsigned int i = 1; i < lh->opcode_base; ++i)
    {
      if (line_ptr + 1 > line_end)
	{
	  _bfd_error_handler(_("DWARF error: ran out of room reading standard opcode lengths"));
	  bfd_set_error(bfd_error_bad_value);
	  return false;
	}
      lh->standard_opcode_lengths[i] = read_1_byte(abfd, &line_ptr, line_end);
    }

  *line_ptr_p = line_ptr;
  return true;
}

static bool
bfd_dwarf2_read_line_tables(struct comp_unit *unit, bfd_byte **line_ptr_p,
                            bfd_byte *line_end, struct line_info_table *table,
                            unsigned int dwarf_version)
{
  bfd_byte *line_ptr = *line_ptr_p;
  bfd *abfd = unit->abfd;
  char *cur_file, *cur_dir;
  unsigned int dir, xtime, size;

  if (dwarf_version >= 5)
    {
      if (!read_formatted_entries(unit, &line_ptr, line_end, table,
                                  line_info_add_include_dir_stub))
        return false;

      if (!read_formatted_entries(unit, &line_ptr, line_end, table,
                                  line_info_add_file_name))
        return false;
      table->use_dir_and_file_0 = true;
    }
  else
    {
      while ((cur_dir = read_string(&line_ptr, line_end)) != NULL)
	{
	  if (!line_info_add_include_dir(table, cur_dir))
	    return false;
	}
      if (bfd_get_error() != bfd_error_no_error) /* Catch error if read_string failed */
          return false;

      while ((cur_file = read_string(&line_ptr, line_end)) != NULL)
	{
	  dir = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
	  xtime = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
	  size = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
          if (bfd_get_error() != bfd_error_no_error)
              return false;

	  if (!line_info_add_file_name(table, cur_file, dir, xtime, size))
	    return false;
	}
      if (bfd_get_error() != bfd_error_no_error) /* Catch error if read_string failed */
          return false;
      table->use_dir_and_file_0 = false;
    }

  *line_ptr_p = line_ptr;
  return true;
}

static bool
bfd_dwarf2_process_line_sequence(struct comp_unit *unit, bfd_byte **line_ptr_p,
                                 bfd_byte *line_end, const struct line_head *lh,
                                 struct line_info_table *table)
{
  bfd_byte *line_ptr = *line_ptr_p;
  bfd *abfd = unit->abfd;
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
  unsigned char op_code, extended_op;
  unsigned int exop_len;
  unsigned int dir, xtime, size;

  if (table->num_files > 0)
    {
      filename = concat_filename(table, 1);
      if (filename == NULL)
        {
          /* concat_filename should set bfd_error */
          return false;
        }
    }

  while (!end_sequence && line_ptr < line_end)
    {
      if (line_ptr + 1 > line_end)
        {
          _bfd_error_handler(_("DWARF error: ran out of room reading line op_code"));
          bfd_set_error(bfd_error_bad_value);
          goto line_fail_cleanup_filename;
        }
      op_code = read_1_byte(abfd, &line_ptr, line_end);

      if (op_code >= lh->opcode_base)
	{
	  unsigned char adj_opcode = op_code - lh->opcode_base;
	  if (lh->line_range == 0)
	    {
	      _bfd_error_handler(_("DWARF error: line range is zero for special opcode"));
	      bfd_set_error(bfd_error_bad_value);
	      goto line_fail_cleanup_filename;
	    }

	  if (lh->maximum_ops_per_insn == 1)
	    address += (adj_opcode / lh->line_range
			* lh->minimum_instruction_length);
	  else
	    {
	      address += ((op_index + adj_opcode / lh->line_range)
			  / lh->maximum_ops_per_insn
			  * lh->minimum_instruction_length);
	      op_index = ((op_index + adj_opcode / lh->line_range)
			  % lh->maximum_ops_per_insn);
	    }
	  line += lh->line_base + (adj_opcode % lh->line_range);

	  if (!add_line_info(table, address, op_index, filename,
			      line, column, discriminator, 0))
	    goto line_fail_cleanup_filename;
	  discriminator = 0;
	  if (address < low_pc)
	    low_pc = address;
	  if (address > high_pc)
	    high_pc = address;
	}
      else
	switch (op_code)
	  {
	  case DW_LNS_extended_op:
	    exop_len = _bfd_safe_read_leb128(abfd, &line_ptr,
						    false, line_end);
            if (bfd_get_error() != bfd_error_no_error)
                goto line_fail_cleanup_filename;

            if (line_ptr + exop_len > line_end)
              {
                _bfd_error_handler(_("DWARF error: ran out of room for extended opcode data"));
                bfd_set_error(bfd_error_bad_value);
                goto line_fail_cleanup_filename;
              }
	    extended_op = read_1_byte(abfd, &line_ptr, line_end);

	    switch (extended_op)
	      {
	      case DW_LNE_end_sequence:
		end_sequence = 1;
		if (!add_line_info(table, address, op_index, filename, line,
				    column, discriminator, end_sequence))
		  goto line_fail_cleanup_filename;
		discriminator = 0;
		if (address < low_pc)
		  low_pc = address;
		if (address > high_pc)
		  high_pc = address;
		if (!arange_add(unit, &unit->arange, &unit->file->trie_root,
				 low_pc, high_pc))
		  goto line_fail_cleanup_filename;
		break;
	      case DW_LNE_set_address:
		address = read_address(unit, &line_ptr, line_end);
                if (bfd_get_error() != bfd_error_no_error)
                  goto line_fail_cleanup_filename;
		op_index = 0;
		break;
	      case DW_LNE_define_file:
		cur_file = read_string(&line_ptr, line_end);
                if (bfd_get_error() != bfd_error_no_error)
                    goto line_fail_cleanup_filename;
		dir = _bfd_safe_read_leb128(abfd, &line_ptr,
					    false, line_end);
		xtime = _bfd_safe_read_leb128(abfd, &line_ptr,
						 false, line_end);
		size = _bfd_safe_read_leb128(abfd, &line_ptr,
						false, line_end);
                if (bfd_get_error() != bfd_error_no_error)
                    goto line_fail_cleanup_filename;
		if (!line_info_add_file_name(table, cur_file, dir,
					      xtime, size))
		  goto line_fail_cleanup_filename;
		break;
	      case DW_LNE_set_discriminator:
		discriminator = _bfd_safe_read_leb128(abfd, &line_ptr,
							    false, line_end);
                if (bfd_get_error() != bfd_error_no_error)
                    goto line_fail_cleanup_filename;
		break;
	      case DW_LNE_HP_source_file_correlation:
		line_ptr += (exop_len - 1);
                if (line_ptr > line_end)
                  {
                    _bfd_error_handler(_("DWARF error: HP source file correlation data extends beyond bounds"));
                    bfd_set_error(bfd_error_bad_value);
                    goto line_fail_cleanup_filename;
                  }
		break;
	      default:
		_bfd_error_handler
		  (_("DWARF error: unhandled extended line number opcode 0x%x"), extended_op);
		bfd_set_error(bfd_error_bad_value);
		goto line_fail_cleanup_filename;
	      }
	    break;
	  case DW_LNS_copy:
	    if (!add_line_info(table, address, op_index,
				filename, line, column, discriminator, 0))
		goto line_fail_cleanup_filename;
	    discriminator = 0;
	    if (address < low_pc)
	      low_pc = address;
	    if (address > high_pc)
	      high_pc = address;
	    break;
	  case DW_LNS_advance_pc:
            {
              bfd_vma advance_val = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
              if (bfd_get_error() != bfd_error_no_error)
                  goto line_fail_cleanup_filename;

	      if (lh->maximum_ops_per_insn == 1)
		address += (lh->minimum_instruction_length * advance_val);
	      else
		{
		  address += ((op_index + advance_val) / lh->maximum_ops_per_insn
			       * lh->minimum_instruction_length);
		  op_index = (op_index + advance_val) % lh->maximum_ops_per_insn;
		}
            }
	    break;
	  case DW_LNS_advance_line:
	    line += _bfd_safe_read_leb128(abfd, &line_ptr, true, line_end);
            if (bfd_get_error() != bfd_error_no_error)
                goto line_fail_cleanup_filename;
	    break;
	  case DW_LNS_set_file:
	    {
	      unsigned int filenum = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
              if (bfd_get_error() != bfd_error_no_error)
                  goto line_fail_cleanup_filename;
	      free(filename);
	      filename = concat_filename(table, filenum);
              if (filename == NULL)
                goto line_fail_cleanup_filename;
	      break;
	    }
	  case DW_LNS_set_column:
	    column = _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
            if (bfd_get_error() != bfd_error_no_error)
                goto line_fail_cleanup_filename;
	    break;
	  case DW_LNS_negate_stmt:
	    is_stmt = (!is_stmt);
	    break;
	  case DW_LNS_set_basic_block:
	    break;
	  case DW_LNS_const_add_pc:
	    if (lh->line_range == 0)
	      {
		_bfd_error_handler(_("DWARF error: line range is zero for const_add_pc"));
		bfd_set_error(bfd_error_bad_value);
		goto line_fail_cleanup_filename;
	      }
	    if (lh->maximum_ops_per_insn == 1)
		address += (lh->minimum_instruction_length
			    * ((255 - lh->opcode_base) / lh->line_range));
	    else
		{
		  bfd_vma adjust = ((255 - lh->opcode_base) / lh->line_range);
		  address += (lh->minimum_instruction_length
			      * ((op_index + adjust)
				 / lh->maximum_ops_per_insn));
		  op_index = (op_index + adjust) % lh->maximum_ops_per_insn;
		}
	    break;
	  case DW_LNS_fixed_advance_pc:
	    if (line_ptr + 2 > line_end)
	      {
		_bfd_error_handler(_("DWARF error: ran out of room for fixed_advance_pc"));
		bfd_set_error(bfd_error_bad_value);
		goto line_fail_cleanup_filename;
	      }
	    address += read_2_bytes(abfd, &line_ptr, line_end);
	    op_index = 0;
	    break;
	  default:
            if (op_code < lh->opcode_base && lh->standard_opcode_lengths != NULL)
            {
              unsigned char len = lh->standard_opcode_lengths[op_code];
              for (unsigned int i = 0; i < len; i++)
                {
                  (void) _bfd_safe_read_leb128(abfd, &line_ptr, false, line_end);
                  if (bfd_get_error() != bfd_error_no_error)
                    goto line_fail_cleanup_filename;
                }
            } else {
              _bfd_error_handler(_("DWARF error: unknown opcode 0x%x detected"), op_code);
              bfd_set_error(bfd_error_bad_value);
              goto line_fail_cleanup_filename;
            }
	    break;
	  }
    }

  free(filename);
  *line_ptr_p = line_ptr;
  return true;

line_fail_cleanup_filename:
  free(filename);
  return false;
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
  struct line_head lh;

  memset(&lh, 0, sizeof(struct line_head));

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

  if (!bfd_dwarf2_read_line_info_prologue(abfd, &line_ptr, &line_end, &lh, unit->addr_size))
    goto fail;

  table = (struct line_info_table *) bfd_alloc (abfd, sizeof (struct line_info_table));
  if (table == NULL)
    goto fail;

  memset(table, 0, sizeof(struct line_info_table));
  table->abfd = abfd;
  table->comp_dir = unit->comp_dir;

  if (!bfd_dwarf2_read_line_tables(unit, &line_ptr, line_end, table, lh.version))
    goto fail;

  while (line_ptr < line_end)
    {
      if (!bfd_dwarf2_process_line_sequence(unit, &line_ptr, line_end, &lh, table))
        goto fail;
    }

  if (unit->line_offset == 0)
    file->line_table = table;

  if (sort_line_sequences (table))
    return table;

fail:
  if (table != NULL) {
    while (table->sequences != NULL)
    {
      struct line_sequence* seq = table->sequences;
      table->sequences = table->sequences->prev_sequence;
      free (seq);
    }
    free (table->files);
    free (table->dirs);
  }
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
  *filename_ptr = NULL;

  if (!table) {
    return false;
  }

  struct line_sequence *seq = NULL;
  int low = 0;
  int high = table->num_sequences;
  int found_seq_idx = -1;

  if (table->num_sequences == 0) {
    return false;
  }

  while (low < high)
    {
      int mid = low + (high - low) / 2;
      struct line_sequence *current_seq = &table->sequences[mid];

      if (!current_seq->last_line) {
          return false;
      }

      if (addr < current_seq->low_pc) {
	high = mid;
      } else if (addr >= current_seq->last_line->address) {
	low = mid + 1;
      } else {
	found_seq_idx = mid;
	break;
      }
    }

  if (found_seq_idx == -1) {
    return false;
  }
  seq = &table->sequences[found_seq_idx];

  if (!build_line_info_table (table, seq)) {
    return false;
  }

  if (seq->num_lines == 0 || !seq->line_info_lookup || !seq->line_info_lookup[0]) {
      return false;
  }

  low = 0;
  high = seq->num_lines;
  int target_info_idx = -1;

  while (low < high)
    {
      int mid = low + (high - low) / 2;
      struct line_info *current_info_entry = seq->line_info_lookup[mid];

      if (!current_info_entry) {
          return false;
      }

      if (current_info_entry->address <= addr) {
	target_info_idx = mid;
	low = mid + 1;
      } else {
	high = mid;
      }
    }

  if (target_info_idx == -1) {
    return false;
  }

  struct line_info *info_entry = seq->line_info_lookup[target_info_idx];

  if (!info_entry) {
      return false;
  }

  if (target_info_idx < seq->num_lines - 1) {
      struct line_info *next_info_entry = seq->line_info_lookup[target_info_idx + 1];
      if (!next_info_entry) {
          return false;
      }
      if (addr >= next_info_entry->address) {
          return false;
      }
  } else {
      if (addr >= seq->last_line->address) {
          return false;
      }
  }

  if (info_entry->end_sequence || info_entry == seq->last_line) {
    return false;
  }

  *filename_ptr = info_entry->filename;
  *linenumber_ptr = info_entry->line;
  if (discriminator_ptr) {
    *discriminator_ptr = info_entry->discriminator;
  }
  return true;
}

/* Read in the .debug_ranges section for future reference.  */

static bool
read_debug_ranges (struct comp_unit * unit)
{
  struct dwarf2_debug * const stash = unit->stash;
  struct dwarf2_debug_file * const file = unit->file;

  return read_section (unit->abfd,
                       &stash->debug_sections[debug_ranges],
                       file->syms,
                       0,
                       &file->dwarf_ranges_buffer,
                       &file->dwarf_ranges_size);
}

/* Read in the .debug_rnglists section for future reference.  */

static bool
read_debug_rnglists (struct comp_unit * unit)
{
  if (unit == NULL || unit->stash == NULL || unit->file == NULL)
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
  const struct lookup_funcinfo * lookup1 = (const struct lookup_funcinfo *)a;
  const struct lookup_funcinfo * lookup2 = (const struct lookup_funcinfo *)b;

  int cmp_result;

  cmp_result = (lookup1->low_addr > lookup2->low_addr) - (lookup1->low_addr < lookup2->low_addr);
  if (cmp_result != 0)
    return cmp_result;

  cmp_result = (lookup1->high_addr > lookup2->high_addr) - (lookup1->high_addr < lookup2->high_addr);
  if (cmp_result != 0)
    return cmp_result;

  cmp_result = (lookup1->idx > lookup2->idx) - (lookup1->idx < lookup2->idx);
  return cmp_result;
}

static bool
build_lookup_funcinfo_table (struct comp_unit * unit)
{
  struct lookup_funcinfo *lookup_table = unit->lookup_funcinfo_table;
  size_t num_functions = unit->number_of_functions;
  struct funcinfo *current_func;
  struct lookup_funcinfo *current_entry;
  size_t i;
  struct arange *range;
  bfd_vma low_addr_val, high_addr_val;

  if (lookup_table != NULL || num_functions == 0)
    return true;

  lookup_table = bfd_malloc (num_functions * sizeof (struct lookup_funcinfo));
  if (lookup_table == NULL)
    return false;

  i = num_functions;
  for (current_func = unit->function_table;
       current_func != NULL && i > 0;
       current_func = current_func->prev_func)
    {
      i--;
      current_entry = &lookup_table[i];
      current_entry->funcinfo = current_func;
      current_entry->idx = i;

      low_addr_val  = current_func->arange.low;
      high_addr_val = current_func->arange.high;

      for (range = current_func->arange.next; range != NULL; range = range->next)
	{
	  if (range->low < low_addr_val)
	    low_addr_val = range->low;
	  if (range->high > high_addr_val)
	    high_addr_val = range->high;
	}

      current_entry->low_addr = low_addr_val;
      current_entry->high_addr = high_addr_val;
    }

  BFD_ASSERT (i == 0);

  qsort (lookup_table,
	 num_functions,
	 sizeof (struct lookup_funcinfo),
	 compare_lookup_funcinfos);

  if (num_functions > 0)
    {
      high_addr_val = lookup_table[0].high_addr;
      for (i = 1; i < num_functions; i++)
	{
	  current_entry = &lookup_table[i];
	  if (current_entry->high_addr > high_addr_val)
	    high_addr_val = current_entry->high_addr;
	  else
	    current_entry->high_addr = high_addr_val;
	}
    }

  unit->lookup_funcinfo_table = lookup_table;
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
  if (!unit || !function_ptr)
    return false;

  unsigned int number_of_functions = unit->number_of_functions;
  struct lookup_funcinfo* lookup_funcinfo_entry = NULL;
  struct funcinfo* current_funcinfo = NULL;
  struct funcinfo* best_fit_funcinfo = NULL;
  bfd_vma best_fit_length = (bfd_vma) -1; /* Initialize with max possible value for bfd_vma */
  bfd_size_type low, high, mid, first_candidate_idx;
  struct arange *address_range;

  if (number_of_functions == 0)
    return false;

  if (!build_lookup_funcinfo_table (unit))
    return false;

  /* Ensure the lookup table pointer is valid after construction. */
  if (!unit->lookup_funcinfo_table)
    return false;

  /* Check if the address is beyond the highest range in the lookup table. */
  if (unit->lookup_funcinfo_table[number_of_functions - 1].high_addr <= addr)
    return false;

  /* Find the first function in the lookup table which may contain the
     specified address using a modified binary search.  */
  low = 0;
  high = number_of_functions;
  first_candidate_idx = high;
  while (low < high)
    {
      mid = low + (high - low) / 2; /* Safer mid calculation to prevent overflow */
      lookup_funcinfo_entry = &unit->lookup_funcinfo_table[mid];
      if (addr < lookup_funcinfo_entry->low_addr)
	high = mid;
      else if (addr >= lookup_funcinfo_entry->high_addr)
	low = mid + 1;
      else
	{
	  high = mid;
	  first_candidate_idx = mid;
	}
    }

  /* Find the 'best' match for the address. The best match is defined as
     the function with the smallest address range containing the specified
     address. In case of a tie in length, a specific tie-breaking rule
     (funcinfo pointer comparison) is applied to maintain backward compatibility. */
  while (first_candidate_idx < number_of_functions)
    {
      if (addr < unit->lookup_funcinfo_table[first_candidate_idx].low_addr)
	break; /* Address is before the current lookup entry's range, so no more candidates */

      current_funcinfo = unit->lookup_funcinfo_table[first_candidate_idx].funcinfo;

      for (address_range = &current_funcinfo->arange; address_range; address_range = address_range->next)
	{
	  if (addr < address_range->low || addr >= address_range->high)
	    continue; /* Address is not within this specific range */

	  bfd_vma current_range_length = address_range->high - address_range->low;

	  if (current_range_length < best_fit_length
	      || (current_range_length == best_fit_length && current_funcinfo > best_fit_funcinfo))
	    {
	      best_fit_funcinfo = current_funcinfo;
	      best_fit_length = current_range_length;
	    }
	}

      first_candidate_idx++;
    }

  if (!best_fit_funcinfo)
    return false;

  *function_ptr = best_fit_funcinfo;
  return true;
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
    {
      return false; /* Invalid input pointers */
    }

  const char *name = bfd_asymbol_name (sym);
  if (name == NULL)
    {
      return false; /* Symbol name is not available */
    }

  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1; /* Represents the maximum possible value for bfd_vma */

  for (struct funcinfo *each = unit->function_table; each; each = each->prev_func)
    {
      if (each->file == NULL || each->name == NULL)
        {
          continue; /* Skip if essential funcinfo data (file or name) is missing */
        }

      for (struct arange *arange = &each->arange; arange; arange = arange->next)
        {
          /* Check if the address falls within the current range */
          if (!(addr >= arange->low && addr < arange->high))
            {
              continue;
            }

          bfd_vma current_range_len = arange->high - arange->low;

          /* Check if this range is strictly smaller than the current best fit */
          if (current_range_len >= best_fit_len)
            {
              continue;
            }

          /* Check if the symbol name contains the function name */
          if (strstr (name, each->name) == NULL)
            {
              continue;
            }

          /* All conditions met, this is a new best fit candidate */
          best_fit = each;
          best_fit_len = current_range_len;
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
  // Validate the input symbol pointer.
  // Passing a NULL 'sym' to bfd_asymbol_name could lead to undefined behavior or crashes.
  if (sym == NULL)
    {
      return false;
    }

  const char *symbol_name = bfd_asymbol_name (sym);

  // Validate the retrieved symbol name.
  // If the symbol has no name (bfd_asymbol_name returns NULL),
  // it cannot match any variable, and calling strstr with a NULL string
  // as the first argument would result in a segmentation fault.
  if (symbol_name == NULL)
    {
      return false;
    }

  // Iterate through the linked list of variable information.
  // Explicitly use 'NULL' for clarity in loop termination.
  for (struct varinfo* each = unit->variable_table; each != NULL; each = each->prev_var)
    {
      // Check all conditions for a match within the current variable entry.
      // Conditions include address, stack status, and availability of file/name,
      // followed by a partial string match for the name.
      // The checks for 'each->file != NULL' and 'each->name != NULL' ensure
      // these pointers are valid before being dereferenced by strstr or assigned.
      if (each->addr == addr
	  && !each->stack
	  && each->file != NULL
	  && each->name != NULL
	  && strstr (symbol_name, each->name) != NULL)
        {
          // A matching variable entry has been found.
          // Populate the output parameters and indicate success.
          // It is assumed that 'filename_ptr' and 'linenumber_ptr' are valid,
          // non-NULL pointers provided by the caller as per C convention.
          *filename_ptr = each->file;
          *linenumber_ptr = each->line;
          return true;
        }
    }

  // No matching variable entry was found after traversing the entire table.
  return false;
}

static struct comp_unit *stash_comp_unit (struct dwarf2_debug *,
					  struct dwarf2_debug_file *);
static bool comp_unit_maybe_decode_line_info (struct comp_unit *);

#define DWARF_ERROR_REPORT(msg) \
  do { \
    _bfd_error_handler (msg); \
    bfd_set_error (bfd_error_bad_value); \
  } while (0)

#define DWARF_ERROR_REPORT_FMT(msg, ...) \
  do { \
    _bfd_error_handler (msg, __VA_ARGS__); \
    bfd_set_error (bfd_error_bad_value); \
  } while (0)

static bool
get_die_and_cu_pointers(struct comp_unit **punit_out,
                        const struct attribute *attr_ptr,
                        uint64_t die_ref,
                        bfd_byte **info_ptr_out,
                        bfd_byte **info_ptr_end_out)
{
  struct comp_unit *current_unit = *punit_out;

  if (attr_ptr->form == DW_FORM_ref_addr)
    {
      bfd_byte *file_info_buffer = current_unit->file->dwarf_info_buffer;
      size_t file_info_size = current_unit->file->dwarf_info_size;

      if (die_ref >= file_info_size)
        {
          DWARF_ERROR_REPORT (_("DWARF error: invalid abstract instance DIE ref (DW_FORM_ref_addr)"));
          return false;
        }
      *info_ptr_out = file_info_buffer + die_ref;
      *info_ptr_end_out = file_info_buffer + file_info_size;
    }
  else if (attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      bool first_time = current_unit->stash->alt.dwarf_info_buffer == NULL;
      bfd_byte *alt_info_ptr = read_alt_indirect_ref (current_unit, die_ref);

      if (first_time)
        current_unit->stash->alt.info_ptr = current_unit->stash->alt.dwarf_info_buffer;
      if (alt_info_ptr == NULL)
        {
          DWARF_ERROR_REPORT_FMT (_("DWARF error: unable to read alt ref %" PRIu64), die_ref);
          return false;
        }
      *info_ptr_out = alt_info_ptr;
      *info_ptr_end_out = (current_unit->stash->alt.dwarf_info_buffer
                           + current_unit->stash->alt.dwarf_info_size);
      if (current_unit->stash->alt.all_comp_units)
        {
          *punit_out = current_unit->stash->alt.all_comp_units;
          current_unit = *punit_out;
        }
    }
  else /* DW_FORM_ref1, DW_FORM_ref2, DW_FORM_ref4, DW_FORM_ref8 or DW_FORM_ref_udata. */
    {
      size_t cu_total_size = current_unit->end_ptr - current_unit->info_ptr_unit;
      if (die_ref == 0 || die_ref >= cu_total_size)
        {
          DWARF_ERROR_REPORT (_("DWARF error: invalid abstract instance DIE ref (CU relative)"));
          return false;
        }
      *info_ptr_out = current_unit->info_ptr_unit + die_ref;
      *info_ptr_end_out = current_unit->end_ptr;
      return true; /* No CU lookup needed for CU-relative forms */
    }

  /* CU lookup for DW_FORM_ref_addr or DW_FORM_GNU_ref_alt */
  if (*info_ptr_out >= current_unit->info_ptr_unit && *info_ptr_out < current_unit->end_ptr)
    {
      *info_ptr_end_out = current_unit->end_ptr;
      return true;
    }
  else
    {
      struct comp_unit *found_cu = NULL;
      struct addr_range range = { *info_ptr_out, *info_ptr_out };
      splay_tree_node v = splay_tree_lookup (current_unit->file->comp_unit_tree,
                                             (splay_tree_key)&range);
      if (v != NULL)
        found_cu = (struct comp_unit *)v->value;

      if (found_cu == NULL)
        {
          struct dwarf_file *target_file = (attr_ptr->form == DW_FORM_ref_addr)
                                            ? &current_unit->stash->f
                                            : &current_unit->stash->alt;
          while (found_cu == NULL)
            {
              struct comp_unit *u_candidate = stash_comp_unit (current_unit->stash, target_file);
              if (u_candidate == NULL)
                break;
              if (*info_ptr_out >= u_candidate->info_ptr_unit && *info_ptr_out < u_candidate->end_ptr)
                {
                  found_cu = u_candidate;
                  break;
                }
            }
        }

      if (found_cu == NULL)
        {
          DWARF_ERROR_REPORT_FMT (_("DWARF error: unable to locate abstract instance DIE ref %" PRIu64), die_ref);
          return false;
        }
      *punit_out = found_cu;
      *info_ptr_end_out = found_cu->end_ptr;
      return true;
    }
}

static bool
find_abstract_instance (struct comp_unit *unit_arg,
			struct attribute *attr_ptr,
			unsigned int recur_count,
			const char **pname,
			bool *is_linkage,
			char **filename_ptr,
			int *linenumber_ptr)
{
  if (recur_count == 100)
    {
      DWARF_ERROR_REPORT (_("DWARF error: abstract instance recursion detected"));
      return false;
    }

  uint64_t die_ref = attr_ptr->u.val;
  bfd_byte *die_info_ptr = NULL;
  bfd_byte *die_info_ptr_end = NULL;
  struct comp_unit *current_unit = unit_arg;

  if (attr_ptr->form == DW_FORM_ref_addr && die_ref == 0)
    return true;

  if (!get_die_and_cu_pointers(&current_unit, attr_ptr, die_ref,
                               &die_info_ptr, &die_info_ptr_end))
    return false;

  unsigned int abbrev_number = _bfd_safe_read_leb128 (current_unit->abfd, &die_info_ptr,
                                                     false, die_info_ptr_end);
  if (abbrev_number == (unsigned int) -1 || die_info_ptr > die_info_ptr_end)
    {
      DWARF_ERROR_REPORT (_("DWARF error: failed to read abbreviation number"));
      return false;
    }
  if (abbrev_number == 0)
    return true;

  struct abbrev_info *abbrev = lookup_abbrev (abbrev_number, current_unit->abbrevs);
  if (!abbrev)
    {
      DWARF_ERROR_REPORT_FMT (_("DWARF error: could not find abbrev number %u"), abbrev_number);
      return false;
    }

  for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      bfd_byte *next_info_ptr = read_attribute (&attr, &abbrev->attrs[i], current_unit,
                                               die_info_ptr, die_info_ptr_end);
      if (next_info_ptr == NULL)
        {
          DWARF_ERROR_REPORT (_("DWARF error: failed to read attribute"));
          return false;
        }

      die_info_ptr = next_info_ptr;

      switch (attr.name)
        {
        case DW_AT_name:
          if (*pname == NULL && is_str_form (&attr))
            {
              *pname = attr.u.str;
              if (mangle_style (current_unit->lang) == 0)
                *is_linkage = true;
            }
          break;
        case DW_AT_specification:
          if (is_int_form (&attr)
              && !find_abstract_instance (current_unit, &attr, recur_count + 1,
                                          pname, is_linkage,
                                          filename_ptr, linenumber_ptr))
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
          if (is_int_form (&attr))
            {
              if (!comp_unit_maybe_decode_line_info (current_unit))
                return false;
              free (*filename_ptr);
              *filename_ptr = concat_filename (current_unit->line_table,
                                               attr.u.val);
              if (*filename_ptr == NULL)
                {
                  bfd_set_error (bfd_error_no_memory);
                  return false;
                }
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

static bool
read_ranges (struct comp_unit *unit, struct arange *arange,
	     struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *ranges_ptr;
  bfd_byte *ranges_end;
  bfd_vma base_address = unit->base_address;

  if (unit->file->dwarf_ranges_buffer == NULL)
    {
      if (!read_debug_ranges (unit))
	return false;
    }

  if (offset > unit->file->dwarf_ranges_size)
    return false;

  ranges_ptr = unit->file->dwarf_ranges_buffer + offset;
  ranges_end = unit->file->dwarf_ranges_buffer + unit->file->dwarf_ranges_size;

  const unsigned int NUM_ADDR_IN_PAIR = 2;
  const size_t REQUIRED_BYTES_PER_PAIR = NUM_ADDR_IN_PAIR * unit->addr_size;

  for (;;)
    {
      if ((size_t)(ranges_end - ranges_ptr) < REQUIRED_BYTES_PER_PAIR)
	return false;

      bfd_vma low_pc = read_address (unit, &ranges_ptr, ranges_end);
      bfd_vma high_pc = read_address (unit, &ranges_ptr, ranges_end);

      if (low_pc == 0 && high_pc == 0)
	break;

      if (low_pc == (bfd_vma) -1 && high_pc != (bfd_vma) -1)
	base_address = high_pc;
      else
	{
	  if (!arange_add (unit, arange, trie_root,
			   base_address + low_pc, base_address + high_pc))
	    return false;
	}
    }
  return true;
}

static bool
read_rnglists (struct comp_unit *unit, struct arange *arange,
	       struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *rngs_ptr;
  bfd_byte *rngs_end;
  bfd_vma base_address;
  bfd_vma low_pc;
  bfd_vma high_pc;
  bfd *abfd = unit->abfd;
  const size_t addr_size = unit->addr_size;

  if (!unit->file->dwarf_rnglists_buffer)
    {
      if (!read_debug_rnglists (unit))
	return false;
    }

  rngs_ptr = unit->file->dwarf_rnglists_buffer + offset;
  rngs_end = unit->file->dwarf_rnglists_buffer + unit->file->dwarf_rnglists_size;

  if (rngs_ptr < unit->file->dwarf_rnglists_buffer || rngs_ptr > rngs_end)
    return false;

  base_address = unit->base_address;

  for (;;)
    {
      enum dwarf_range_list_entry rlet;
      size_t current_bytes_remaining = rngs_end - rngs_ptr;

      if (current_bytes_remaining < 1)
	return false;

      rlet = read_1_byte (abfd, &rngs_ptr, rngs_end);

      current_bytes_remaining = rngs_end - rngs_ptr;

      switch (rlet)
	{
	case DW_RLE_end_of_list:
	  return true;

	case DW_RLE_base_address:
	  if (current_bytes_remaining < addr_size)
	    return false;
	  base_address = read_address (unit, &rngs_ptr, rngs_end);
	  continue;

	case DW_RLE_start_length:
	  if (current_bytes_remaining < addr_size)
	    return false;
	  low_pc = read_address (unit, &rngs_ptr, rngs_end);
	  high_pc = low_pc + _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	  break;

	case DW_RLE_offset_pair:
	  low_pc = base_address + _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	  high_pc = base_address + _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	  break;

	case DW_RLE_start_end:
	  if (current_bytes_remaining < 2 * addr_size)
	    return false;
	  low_pc = read_address (unit, &rngs_ptr, rngs_end);
	  high_pc = read_address (unit, &rngs_ptr, rngs_end);
	  break;

	case DW_RLE_base_addressx:
	case DW_RLE_startx_endx:
	case DW_RLE_startx_length:
	default:
	  return false;
	}

      if (!arange_add (unit, arange, trie_root, low_pc, high_pc))
	return false;
    }
}

#define UNIT_VERSION_LEGACY_THRESHOLD 4

static bool
read_rangelist (struct comp_unit *unit, struct arange *arange,
		struct trie_node **trie_root, uint64_t offset)
{
  if (unit->version <= UNIT_VERSION_LEGACY_THRESHOLD)
    return read_ranges (unit, arange, trie_root, offset);
  else
    return read_rnglists (unit, arange, trie_root, offset);
}

static struct funcinfo *
lookup_func_by_offset (uint64_t offset, const struct funcinfo *head)
{
  for (const struct funcinfo *current_func_node = head;
       current_func_node != NULL;
       current_func_node = current_func_node->prev_func)
  {
    if (current_func_node->unit_offset == offset)
      return (struct funcinfo *)current_func_node;
  }
  return NULL;
}

static struct varinfo *
lookup_var_by_offset (uint64_t offset, struct varinfo * head)
{
  for (struct varinfo *current = head; current != NULL; current = current->prev_var)
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
  struct funcinfo *reversed_head = NULL;
  struct funcinfo *current = head;
  struct funcinfo *next_node;

  while (current != NULL)
    {
      next_node = current->prev_func;
      current->prev_func = reversed_head;
      reversed_head = current;
      current = next_node;
    }
  return reversed_head;
}

static struct varinfo *
reverse_varinfo_list (struct varinfo *current)
{
  struct varinfo *prev = NULL;
  struct varinfo *next_node;

  while (current != NULL)
    {
      next_node = current->prev_var;
      current->prev_var = prev;
      prev = current;
      current = next_node;
    }
  return prev;
}

/* Scan over each die in a comp. unit looking for functions to add
   to the function table and variables to the variable table.  */

struct nest_funcinfo
{
  struct funcinfo *func;
};

static bool
grow_nested_funcs_stack(struct nest_funcinfo **nested_funcs_ptr, int *size_ptr, int current_level)
{
  if (current_level < *size_ptr)
    return true;

  int new_size = *size_ptr * 2;
  struct nest_funcinfo *tmp = (struct nest_funcinfo *)
    bfd_realloc (*nested_funcs_ptr, new_size * sizeof (**nested_funcs_ptr));
  if (tmp == NULL)
    return false;

  *nested_funcs_ptr = tmp;
  *size_ptr = new_size;
  return true;
}

static bool
process_func_attribute(struct comp_unit *unit, struct funcinfo *func, const struct attribute *attr,
                       bfd_vma *low_pc_ptr, bfd_vma *high_pc_ptr, bool *high_pc_relative_ptr)
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
        *low_pc_ptr = attr->u.val;
      break;

    case DW_AT_high_pc:
      if (is_int_form (attr))
        {
          *high_pc_ptr = attr->u.val;
          *high_pc_relative_ptr = attr->form != DW_FORM_addr;
        }
      break;

    case DW_AT_ranges:
      if (is_int_form (attr)
          && !read_rangelist (unit, &func->arange, &unit->file->trie_root, attr->u.val))
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
process_var_attribute(struct comp_unit *unit, struct varinfo *var, const struct attribute *attr)
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
      switch (attr->form)
        {
        case DW_FORM_block:
        case DW_FORM_block1:
        case DW_FORM_block2:
        case DW_FORM_block4:
        case DW_FORM_exprloc:
          if (attr->u.blk != NULL
              && attr->u.blk->data != NULL
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
      break;

    default:
      break;
    }
}

static bool
scan_unit_for_symbols (struct comp_unit *unit)
{
  bfd *abfd = unit->abfd;
  bfd_byte *info_ptr = unit->first_child_die_ptr;
  bfd_byte *info_ptr_end = unit->end_ptr;
  int nesting_level = 0;
  struct nest_funcinfo *nested_funcs = NULL;
  int nested_funcs_size;
  
  nested_funcs_size = 32;
  nested_funcs = (struct nest_funcinfo *)
    bfd_malloc (nested_funcs_size * sizeof (*nested_funcs));
  if (nested_funcs == NULL)
    goto fail;
  nested_funcs[0].func = NULL; // Initialize base level.

  /* Pass 1: Scan for function and variable tags and accumulate them into
     their respective tables.  */
  bfd_byte *current_info_ptr = info_ptr;
  int current_nesting_level = nesting_level;

  while (current_nesting_level >= 0)
    {
      if (current_info_ptr >= info_ptr_end)
	goto fail;

      uint64_t current_offset = current_info_ptr - unit->info_ptr_unit;
      unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &current_info_ptr, false, info_ptr_end);

      if (abbrev_number == 0)
	{
	  current_nesting_level--;
	  continue;
	}

      struct abbrev_info *abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
      if (abbrev == NULL)
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
	  goto fail;
	}

      struct funcinfo *func = NULL;

      if (abbrev->tag == DW_TAG_subprogram
	  || abbrev->tag == DW_TAG_entry_point
	  || abbrev->tag == DW_TAG_inlined_subroutine)
	{
	  func = (struct funcinfo *) bfd_zalloc (abfd, sizeof (struct funcinfo));
	  if (func == NULL)
	    goto fail;

	  func->tag = abbrev->tag;
	  func->prev_func = unit->function_table;
	  func->unit_offset = current_offset;
	  unit->function_table = func;
	  unit->number_of_functions++;
	  BFD_ASSERT (!unit->cached);

	  if (func->tag == DW_TAG_inlined_subroutine)
	    for (int i = current_nesting_level; i-- != 0; )
	      if (nested_funcs[i].func)
		{
		  func->caller_func = nested_funcs[i].func;
		  break;
		}
	  nested_funcs[current_nesting_level].func = func;
	}
      else if (abbrev->tag == DW_TAG_variable
	       || abbrev->tag == DW_TAG_member)
	{
	  struct varinfo *var = (struct varinfo *) bfd_zalloc (abfd, sizeof (struct varinfo));
	  if (var == NULL)
		goto fail;

	  var->tag = abbrev->tag;
	  var->stack = true;
	  var->prev_var = unit->variable_table;
	  unit->variable_table = var;
	  var->unit_offset = current_offset;
	}
      else
	{
	  nested_funcs[current_nesting_level].func = NULL;
	}

      for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
	{
	  struct attribute attr_temp;
	  current_info_ptr = read_attribute (&attr_temp, &abbrev->attrs[i],
                                             unit, current_info_ptr, info_ptr_end);
	  if (current_info_ptr == NULL)
	    goto fail;
	}

      if (abbrev->has_children)
	{
	  current_nesting_level++;
	  if (!grow_nested_funcs_stack(&nested_funcs, &nested_funcs_size, current_nesting_level))
	    goto fail;
	  nested_funcs[current_nesting_level].func = NULL;
	}
    }

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  /* Pass 2: Process attributes of the functions/variables and augment the
     table entries.  */
  info_ptr = unit->first_child_die_ptr;
  nesting_level = 0;
  
  struct funcinfo *last_func = NULL;
  struct varinfo *last_var = NULL;

  while (nesting_level >= 0)
    {
      if (info_ptr >= info_ptr_end)
	goto fail;

      uint64_t current_offset = info_ptr - unit->info_ptr_unit;
      unsigned int abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      if (abbrev_number == 0)
	{
	  nesting_level--;
	  continue;
	}

      struct abbrev_info *abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
      BFD_ASSERT (abbrev != NULL);

      struct funcinfo *func = NULL;
      struct varinfo *var = NULL;
      bfd_vma low_pc = 0;
      bfd_vma high_pc = 0;
      bool high_pc_relative = false;

      if (abbrev->tag == DW_TAG_subprogram
	  || abbrev->tag == DW_TAG_entry_point
	  || abbrev->tag == DW_TAG_inlined_subroutine)
	{
	  if (last_func != NULL
	      && last_func->prev_func != NULL
	      && last_func->prev_func->unit_offset == current_offset)
	    func = last_func->prev_func;
	  else
	    func = lookup_func_by_offset (current_offset, unit->function_table);

	  if (func == NULL)
	    goto fail;

	  last_func = func;
	}
      else if (abbrev->tag == DW_TAG_variable
	       || abbrev->tag == DW_TAG_member)
	{
	  if (last_var != NULL
	      && last_var->prev_var != NULL
	      && last_var->prev_var->unit_offset == current_offset)
	    var = last_var->prev_var;
	  else
	    var = lookup_var_by_offset (current_offset, unit->variable_table);

	  if (var == NULL)
	    goto fail;

	  last_var = var;
	}

      for (unsigned int i = 0; i < abbrev->num_attrs; ++i)
	{
	  struct attribute attr;
	  info_ptr = read_attribute (&attr, &abbrev->attrs[i],
				     unit, info_ptr, info_ptr_end);
	  if (info_ptr == NULL)
	    goto fail;

	  if (func)
	    {
	      if (!process_func_attribute(unit, func, &attr, &low_pc, &high_pc, &high_pc_relative))
		goto fail;
	    }
	  else if (var)
	    {
	      process_var_attribute(unit, var, &attr);
	    }
	}

      if (abbrev->has_children)
	nesting_level++;

      if (high_pc_relative)
	high_pc += low_pc;

      if (func && high_pc != 0)
	{
	  if (!arange_add (unit, &func->arange, &unit->file->trie_root,
			   low_pc, high_pc))
	    goto fail;
	}
    }

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  free (nested_funcs);
  return true;

 fail:
  free (nested_funcs);
  return false;
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
    {
      attr->u.str = (char *) read_indexed_string (attr->u.val, unit);
    }
  if (is_addrx_form (attr->form))
    {
      attr->u.val = read_indexed_address (attr->u.val, unit);
    }

  switch (attr->name)
    {
    case DW_AT_stmt_list:
      unit->stmtlist = 1;
      unit->line_offset = attr->u.val;
      break;

    case DW_AT_name:
      if (is_str_form (attr))
        {
          unit->name = attr->u.str;
        }
      break;

    case DW_AT_low_pc:
      *low_pc = attr->u.val;
      if (compunit)
        {
          unit->base_address = *low_pc;
        }
      break;

    case DW_AT_high_pc:
      *high_pc = attr->u.val;
      *high_pc_relative = attr->form != DW_FORM_addr;
      break;

    case DW_AT_ranges:
      if (!read_rangelist (unit, &unit->arange,
                           &unit->file->trie_root, attr->u.val))
        {
          return; /* Early exit on failure, consistent with existing logic. */
        }
      break;

    case DW_AT_comp_dir:
      {
        char *current_comp_dir_val = attr->u.str;

        if (!is_str_form (attr))
          {
            _bfd_error_handler
              (_("DWARF error: DW_AT_comp_dir attribute encountered "
                 "with a non-string form"));
            unit->comp_dir = NULL; /* Ensure comp_dir is NULL on error. */
          }
        else
          {
            char *colon_pos = strchr (current_comp_dir_val, ':');

            /* Check for a specific pattern like "./:/some/path" and skip the prefix. */
            if (colon_pos != NULL
                && colon_pos != current_comp_dir_val
                && colon_pos[-1] == '.'
                && colon_pos[1] == '/')
              {
                current_comp_dir_val = colon_pos + 1; /* Skip past the colon. */
              }
            unit->comp_dir = current_comp_dir_val;
          }
        break;
      }

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
  struct comp_unit *unit = NULL;
  unsigned int version;
  uint64_t abbrev_offset;
  unsigned int addr_size = 0; /* Initialize to a valid default or 0 for checks. */
  struct abbrev_info **abbrevs = NULL;
  unsigned int abbrev_number;
  struct abbrev_info *abbrev = NULL;
  bfd_byte *end_ptr = info_ptr + unit_length;
  bfd *abfd = file->bfd_ptr;
  enum dwarf_unit_type unit_type;
  struct attribute *str_addr_attrs = NULL;
  size_t str_attr_count = 0;
  size_t str_attr_alloc = 0;
  bool is_comp_unit_die = false;

  version = read_2_bytes (abfd, &info_ptr, end_ptr);
  if (version == 0)
    {
      /* Version 0 probably means padding. Silently return NULL. */
      return NULL;
    }
  if (version < 2 || version > 5)
    {
      _bfd_error_handler
	(_("DWARF error: found DWARF version '%u', this reader"
	   " only handles version 2, 3, 4 and 5 information"), version);
      bfd_set_error (bfd_error_bad_value);
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
      info_ptr += 8; /* Skip type signature. */
      info_ptr += offset_size; /* Skip type offset. */
      break;

    case DW_UT_skeleton:
      info_ptr += 8; /* Skip DWO_id field. */
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
	(_("DWARF error: found address size '%u', this reader"
	   " can only handle address sizes '2', '4' and '8'"), addr_size);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  abbrevs = read_abbrevs (abfd, abbrev_offset, stash, file);
  if (!abbrevs)
    return NULL;

  abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, end_ptr);
  if (abbrev_number == 0)
    {
      /* Abbrev number 0 probably means padding. Silently return NULL. */
      return NULL;
    }

  abbrev = lookup_abbrev (abbrev_number, abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"),
			  abbrev_number);
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

  if (abbrev->tag == DW_TAG_compile_unit)
    is_comp_unit_die = true;

  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bool high_pc_relative = false;
  unsigned int i;

  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      struct attribute attr;
      info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit, info_ptr, end_ptr);
      if (info_ptr == NULL)
	goto err_exit;

      if ((unit->dwarf_str_offset == 0 && is_strx_form (attr.form))
	  || (unit->dwarf_addr_offset == 0 && is_addrx_form (attr.form)))
	{
	  if (str_attr_count >= str_attr_alloc)
	    {
	      str_attr_alloc = (str_attr_alloc == 0) ? 200 : (str_attr_alloc * 2);
	      struct attribute *new_str_addr_attrs = bfd_realloc (str_addr_attrs,
								  str_attr_alloc * sizeof (*str_addr_attrs));
	      if (new_str_addr_attrs == NULL)
		goto err_exit;
	      str_addr_attrs = new_str_addr_attrs;
	    }
	  str_addr_attrs[str_attr_count++] = attr;
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
	      if (is_comp_unit_die)
		unit->base_address = low_pc;
	    }
	  break;

	case DW_AT_high_pc:
	  if (is_int_form (&attr))
	    {
	      high_pc = attr.u.val;
	      high_pc_relative = (attr.form != DW_FORM_addr);
	    }
	  break;

	case DW_AT_ranges:
	  if (is_int_form (&attr) && !read_rangelist (unit, &unit->arange,
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
		if (cp != NULL && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
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

  for (i = 0; i < str_attr_count; ++i)
    reread_attribute (unit, &str_addr_attrs[i], &low_pc, &high_pc,
		      &high_pc_relative, is_comp_unit_die);

  if (high_pc_relative)
    high_pc += low_pc;

  if (high_pc != 0)
    {
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
		       low_pc, high_pc))
	goto err_exit;
    }

  unit->first_child_die_ptr = info_ptr;

  free (str_addr_attrs);
  return unit;

 err_exit:
  if (unit)
    unit->error = 1;
  free (str_addr_attrs);
  /* Free the partially allocated unit as well, to prevent memory leaks */
  free (unit);
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
  if (unit == NULL) {
    return false;
  }

  if (unit->error) {
    return false;
  }

  if (unit->arange.high == 0 || unit->line_table == NULL) {
    return true;
  }

  for (struct arange *current_arange = &unit->arange; current_arange != NULL; current_arange = current_arange->next) {
    if (addr >= current_arange->low && addr < current_arange->high) {
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
  bool line_info_found = false;
  bool func_info_found = false;

  if (!comp_unit_maybe_decode_line_info (unit)) {
    return false;
  }

  if (function_ptr != NULL) {
    *function_ptr = NULL;
  }

  func_info_found = lookup_address_in_function_table (unit, addr, function_ptr);

  if (func_info_found && function_ptr != NULL && *function_ptr != NULL) {
    if ((*function_ptr)->tag == DW_TAG_inlined_subroutine) {
      if (unit->stash != NULL) { /* Defensive check for potential NULL stash */
        unit->stash->inliner_chain = *function_ptr;
      }
    }
  }

  line_info_found = lookup_address_in_line_info_table (unit->line_table, addr,
                                                       filename_ptr,
                                                       linenumber_ptr,
                                                       discriminator_ptr);

  return line_info_found || func_info_found;
}

/* Check to see if line info is already decoded in a comp_unit.
   If not, decode it.  Returns TRUE if no errors were encountered;
   FALSE otherwise.  */

static bool
comp_unit_maybe_decode_line_info (struct comp_unit *unit)
{
  bool success = true;

  if (unit->error)
    return false;

  if (!unit->line_table)
    {
      if (!unit->stmtlist)
        {
          success = false;
        }
      else
        {
          unit->line_table = decode_line_info (unit);
          if (!unit->line_table)
            {
              success = false;
            }
        }

      if (success && unit->first_child_die_ptr < unit->end_ptr)
        {
          if (!scan_unit_for_symbols (unit))
            {
              success = false;
            }
        }

      if (!success)
        {
          unit->error = 1;
        }
    }

  return success;
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
  if (unit == NULL || sym == NULL)
    return false;

  if (filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

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
process_func_list_and_hash(struct funcinfo **list_head_ptr,
                           struct info_hash_table *hash_table)
{
  bool local_okay = true;
  *list_head_ptr = reverse_funcinfo_list(*list_head_ptr);
  struct funcinfo *current_func = *list_head_ptr;
  while (current_func != NULL && local_okay)
    {
      if (current_func->name != NULL)
	local_okay = insert_info_hash_table(hash_table, current_func->name,
					    (void*) current_func, false);
      current_func = current_func->prev_func;
    }
  *list_head_ptr = reverse_funcinfo_list(*list_head_ptr);
  return local_okay;
}

static bool
process_var_list_and_hash(struct varinfo **list_head_ptr,
                          struct info_hash_table *hash_table)
{
  bool local_okay = true;
  *list_head_ptr = reverse_varinfo_list(*list_head_ptr);
  struct varinfo *current_var = *list_head_ptr;
  while (current_var != NULL && local_okay)
    {
      if (!current_var->stack
	  && current_var->file != NULL
	  && current_var->name != NULL)
	local_okay = insert_info_hash_table(hash_table, current_var->name,
					    (void*) current_var, false);
      current_var = current_var->prev_var;
    }
  *list_head_ptr = reverse_varinfo_list(*list_head_ptr);
  return local_okay;
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

  if (!process_func_list_and_hash(&unit->function_table, funcinfo_hash_table))
    return false;

  if (!process_var_list_and_hash(&unit->variable_table, varinfo_hash_table))
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
is_debug_section_match_iterative(asection *msec, const struct dwarf_debug_section *debug_sections)
{
  if (msec == NULL || (msec->flags & SEC_HAS_CONTENTS) == 0)
    return false;

  const char *uncompressed_name = debug_sections[debug_info].uncompressed_name;
  if (uncompressed_name != NULL && strcmp(msec->name, uncompressed_name) == 0)
    return true;

  const char *compressed_name = debug_sections[debug_info].compressed_name;
  if (compressed_name != NULL && strcmp(msec->name, compressed_name) == 0)
    return true;

  if (startswith(msec->name, GNU_LINKONCE_INFO))
    return true;

  return false;
}

static asection *
find_debug_info (bfd *abfd, const struct dwarf_debug_section *debug_sections,
		 asection *after_sec)
{
  if (abfd == NULL || debug_sections == NULL)
    return NULL;

  asection *msec;

  if (after_sec == NULL)
    {
      const char *uncompressed_look = debug_sections[debug_info].uncompressed_name;
      msec = bfd_get_section_by_name(abfd, uncompressed_look);
      if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
        return msec;

      const char *compressed_look = debug_sections[debug_info].compressed_name;
      if (compressed_look != NULL)
        {
          msec = bfd_get_section_by_name(abfd, compressed_look);
          if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
            return msec;
        }

      for (msec = abfd->sections; msec != NULL; msec = msec->next)
        {
          if ((msec->flags & SEC_HAS_CONTENTS) != 0
              && startswith(msec->name, GNU_LINKONCE_INFO))
            return msec;
        }

      return NULL;
    }
  else
    {
      for (msec = after_sec->next; msec != NULL; msec = msec->next)
        {
          if (is_debug_section_match_iterative(msec, debug_sections))
            return msec;
        }
    }

  return NULL;
}

/* Transfer VMAs from object file to separate debug file.  */

static void
set_debug_vma (bfd *orig_bfd, bfd *debug_bfd)
{
  if (orig_bfd == NULL || debug_bfd == NULL)
    {
      return;
    }

  asection *original_section = orig_bfd->sections;
  asection *debug_section = debug_bfd->sections;

  while (original_section != NULL && debug_section != NULL)
    {
      if ((debug_section->flags & SEC_DEBUGGING) != 0)
	{
	  break;
	}

      if (strcmp (original_section->name, debug_section->name) == 0)
	{
	  debug_section->output_section = original_section->output_section;
	  debug_section->output_offset = original_section->output_offset;
	  debug_section->vma = original_section->vma;
	}

      original_section = original_section->next;
      debug_section = debug_section->next;
    }
}

/* If the dwarf2 info was found in a separate debug file, return the
   debug file section corresponding to the section in the original file
   and the debug file symbols.  */

static void
_bfd_dwarf2_stash_syms (struct dwarf2_debug *stash, bfd *abfd,
			asection **sec_ptr, asymbol ***syms_ptr)
{
  if (stash->f.bfd_ptr != abfd)
    {
      if (*sec_ptr == NULL)
	{
	  *syms_ptr = stash->f.syms;
	  return;
	}

      if (stash->f.bfd_ptr == NULL)
        {
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

	  if (s == *sec_ptr && strcmp (s->name, d->name) == 0)
	    {
	      *sec_ptr = d;
	      *syms_ptr = stash->f.syms;
	      break;
	    }
	}
    }
}

/* Unset vmas for adjusted sections in STASH.  */

static void
unset_sections (struct dwarf2_debug *stash)
{
  if (stash == NULL) {
    return;
  }

  int section_count = stash->adjusted_section_count;
  struct adjusted_section *sections_ptr = stash->adjusted_sections;

  if (section_count <= 0 || sections_ptr == NULL) {
    return;
  }

  struct adjusted_section *end_ptr = sections_ptr + section_count;

  for (struct adjusted_section *current_section = sections_ptr;
       current_section < end_ptr;
       ++current_section)
  {
    if (current_section->section != NULL) {
      current_section->section->vma = current_section->orig_vma;
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
is_section_eligible_for_adjustment(asection *sect, bfd *current_bfd, bfd *orig_bfd, const char *debug_info_name)
{
  // Condition 1: Exclude sections that are merely output placeholders or not debug sections.
  if (sect->output_section != NULL
      && sect->output_section != sect
      && (sect->flags & SEC_DEBUGGING) == 0)
    {
      return false;
    }

  // Condition 2: Check if it's a debug_info section or an allocated section from the original BFD.
  bool is_debug_info_section = (strcmp (sect->name, debug_info_name) == 0
                                || startswith (sect->name, GNU_LINKONCE_INFO));

  bool is_allocated_orig_bfd = ((sect->flags & SEC_ALLOC) != 0 && current_bfd == orig_bfd);

  return is_debug_info_section || is_allocated_orig_bfd;
}

static bool
place_sections (bfd *orig_bfd, struct dwarf2_debug *stash)
{
  // Early exit if sections are already adjusted (positive count) or
  // if adjustment was previously determined to be unnecessary (negative count).
  if (stash->adjusted_section_count > 0)
    {
      struct adjusted_section *p_adj = stash->adjusted_sections;
      for (int i = 0; i < stash->adjusted_section_count; i++, p_adj++)
        p_adj->section->vma = p_adj->adj_vma;
      return true;
    }
  else if (stash->adjusted_section_count < 0)
    {
      // No adjustment needed/possible, as determined by a previous run.
      return true;
    }

  // Proceed with calculation if stash->adjusted_section_count is 0.

  const char *debug_info_name = stash->debug_sections[debug_info].uncompressed_name;
  int section_count = 0;

  // Prepare the list of BFDs to process.
  // The original loop structure processes orig_bfd, then stash->f.bfd_ptr if different.
  bfd *bfds_to_process[2];
  int bfd_num_to_process = 0;

  bfds_to_process[bfd_num_to_process++] = orig_bfd;
  if (orig_bfd != stash->f.bfd_ptr)
    {
      bfds_to_process[bfd_num_to_process++] = stash->f.bfd_ptr;
    }

  // First pass: Count eligible sections to determine allocation size.
  for (int k = 0; k < bfd_num_to_process; k++)
    {
      bfd *current_bfd = bfds_to_process[k];
      for (asection *sect = current_bfd->sections; sect != NULL; sect = sect->next)
        {
          if (is_section_eligible_for_adjustment(sect, current_bfd, orig_bfd, debug_info_name))
            {
              section_count++;
            }
        }
    }

  // If 1 or fewer sections, no meaningful adjustment is needed.
  if (section_count <= 1)
    {
      stash->adjusted_section_count = -1; // Mark as permanently no adjustments needed.
      return true;
    }

  // Allocate memory for adjusted_sections.
  size_t amt = section_count * sizeof (struct adjusted_section);
  struct adjusted_section *p_adj = (struct adjusted_section *) bfd_malloc (amt);
  if (p_adj == NULL)
    {
      // Memory allocation failed. Return false to indicate error.
      // stash->adjusted_section_count remains 0, so a subsequent call will retry.
      return false;
    }

  stash->adjusted_sections = p_adj;
  stash->adjusted_section_count = section_count;

  bfd_vma last_vma = 0;
  bfd_vma last_dwarf = 0;

  // Second pass: Populate adjusted_sections and update section VMAs.
  for (int k = 0; k < bfd_num_to_process; k++)
    {
      bfd *current_bfd = bfds_to_process[k];
      for (asection *sect = current_bfd->sections; sect != NULL; sect = sect->next)
        {
          if (!is_section_eligible_for_adjustment(sect, current_bfd, orig_bfd, debug_info_name))
            {
              continue;
            }

          bfd_size_type sz = sect->rawsize ? sect->rawsize : sect->size;
          bool is_debug_info_section = (strcmp (sect->name, debug_info_name) == 0
                                        || startswith (sect->name, GNU_LINKONCE_INFO));

          p_adj->section = sect;
          p_adj->orig_vma = sect->vma;

          bfd_vma *current_vma_ptr = is_debug_info_section ? &last_dwarf : &last_vma;

          // Align the new address to the current section alignment.
          bfd_vma alignment = (bfd_vma)1 << sect->alignment_power;
          *current_vma_ptr = (*current_vma_ptr + alignment - 1) & ~(alignment - 1);
          
          sect->vma = *current_vma_ptr;
          *current_vma_ptr += sz;

          p_adj->adj_vma = sect->vma;
          p_adj++;
        }
    }

  // Final step: Call set_debug_vma if needed, as in the original code.
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
  if (hash_table == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    {
      return false;
    }

  const char *name = bfd_asymbol_name (sym);
  if (name == NULL)
    {
      return false;
    }

  struct funcinfo* best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma) -1;

  struct info_list_node *node = lookup_info_hash_table (hash_table, name);

  for (; node != NULL; node = node->next)
    {
      struct funcinfo* each_func = (struct funcinfo *) node->info;
      if (each_func == NULL)
        {
          continue;
        }

      for (struct arange *arange = &each_func->arange; arange != NULL; arange = arange->next)
        {
          if (addr >= arange->low && addr < arange->high)
            {
              bfd_vma current_range_len = arange->high - arange->low;
              if (current_range_len < best_fit_len)
                {
                  best_fit = each_func;
                  best_fit_len = current_range_len;
                }
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
  if (hash_table == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL) {
    return false;
  }

  const char *name = bfd_asymbol_name (sym);
  if (name == NULL) {
    return false;
  }

  struct info_list_node *node;
  struct varinfo* each;

  for (node = lookup_info_hash_table (hash_table, name);
       node != NULL;
       node = node->next)
    {
      if (node->info == NULL) {
        continue;
      }

      each = (struct varinfo *) node->info;

      if (each->addr == addr)
	{
	  *filename_ptr = each->file;
	  *linenumber_ptr = each->line;
	  return true;
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
  if (stash->f.all_comp_units == stash->hash_units_head)
    return true;

  struct comp_unit *current_unit = stash->f.all_comp_units;
  struct comp_unit *stop_at_unit = stash->hash_units_head;

  while (current_unit != stop_at_unit)
    {
      if (!current_unit)
        {
          stash->info_hash_status = STASH_INFO_HASH_DISABLED;
          return false;
        }

      if (!comp_unit_hash_info (stash, current_unit, stash->funcinfo_hash_table,
                                stash->varinfo_hash_table))
        {
          stash->info_hash_status = STASH_INFO_HASH_DISABLED;
          return false;
        }
      current_unit = current_unit->prev_unit;
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

  /* Initialize pointers to NULL before potential allocations.
     This ensures a clean state and avoids stale pointers if allocations fail.  */
  stash->funcinfo_hash_table = NULL;
  stash->varinfo_hash_table = NULL;

  /* Create hash tables.  */
  stash->funcinfo_hash_table = create_info_hash_table (abfd);
  if (!stash->funcinfo_hash_table)
    {
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
      return;
    }

  stash->varinfo_hash_table = create_info_hash_table (abfd);
  if (!stash->varinfo_hash_table)
    {
      /* If the second allocation fails, both hash tables are effectively
         unavailable for this feature. Set the first allocated table's
         pointer to NULL for consistency in the 'stash' state.
         Memory associated with 'funcinfo_hash_table' is presumed to be
         managed by 'abfd' and will be freed upon 'bfd_close' or
         similar BFD lifecycle events.  */
      stash->funcinfo_hash_table = NULL;
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
      return;
    }

  /* We need a forced update so that the info hash tables will
     be created even though there is no compilation unit.  That
     happens if STASH_INFO_HASH_TRIGGER is 0.  */
  if (stash_maybe_update_info_hash_tables (stash))
    stash->info_hash_status = STASH_INFO_HASH_ON;
  /* If stash_maybe_update_info_hash_tables fails, the status remains
     STASH_INFO_HASH_OFF, as per the original logic.  */
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
    {
      return false;
    }

  if (stash->info_hash_status != STASH_INFO_HASH_ON)
    {
      return false;
    }

  if (sym->flags & BSF_FUNCTION)
    {
      return info_hash_lookup_funcinfo (stash->funcinfo_hash_table, sym, addr,
                                        filename_ptr, linenumber_ptr);
    }
  else
    {
      return info_hash_lookup_varinfo (stash->varinfo_hash_table, sym, addr,
                                       filename_ptr, linenumber_ptr);
    }
}

/* Save current section VMAs.  */

static bool
save_section_vma (const bfd *abfd, struct dwarf2_debug *stash)
{
  if (abfd->section_count == 0)
    {
      stash->sec_vma = NULL;
      stash->sec_vma_count = 0;
      return true;
    }

  bfd_vma *section_vma_array = bfd_malloc (sizeof (*section_vma_array) * abfd->section_count);
  if (section_vma_array == NULL)
    {
      stash->sec_vma = NULL;
      stash->sec_vma_count = 0;
      return false;
    }

  unsigned int i;
  asection *s;

  for (i = 0, s = abfd->sections;
       s != NULL && i < abfd->section_count;
       ++i, s = s->next)
    {
      if (s->output_section != NULL)
        {
          section_vma_array[i] = s->output_section->vma + s->output_offset;
        }
      else
        {
          section_vma_array[i] = s->vma;
        }
    }

  stash->sec_vma = section_vma_array;
  stash->sec_vma_count = i;

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
  if (abfd->section_count != stash->sec_vma_count)
    return false;

  asection *current_section = abfd->sections;
  for (unsigned int i = 0; i < abfd->section_count; ++i)
    {
      if (current_section == NULL)
        {
          return false;
        }

      bfd_vma current_vma;
      if (current_section->output_section != NULL)
        {
          current_vma = current_section->output_section->vma + current_section->output_offset;
        }
      else
        {
          current_vma = current_section->vma;
        }

      if (current_vma != stash->sec_vma[i])
        {
          return false;
        }
      
      current_section = current_section->next;
    }

  if (current_section != NULL)
    {
      return false;
    }

  return true;
}

/* Read debug information from DEBUG_BFD when DEBUG_BFD is specified.
   If DEBUG_BFD is not specified, we read debug information from ABFD
   or its gnu_debuglink. The results will be stored in PINFO.
   The function returns TRUE iff debug information is ready.  */

bool
_bfd_dwarf2_slurp_debug_info (bfd *abfd, bfd *debug_bfd_param,
			      const struct dwarf_debug_section *debug_sections,
			      asymbol **symbols_param,
			      void **pinfo,
			      bool do_place)
{
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;
  bool close_debug_bfd_on_cleanup = false;
  bfd *active_debug_bfd = debug_bfd_param;
  asymbol **active_symbols = symbols_param;

  // --- Stash Initialization/Reuse Check ---
  if (stash != NULL)
    {
      if (stash->orig_bfd_id == abfd->id && section_vma_same (abfd, stash))
	{
	  // Check that we did previously find some debug information
	  // before attempting to make use of it.
	  if (stash->f.dwarf_info_size != 0)
	    {
	      if (do_place && !place_sections (abfd, stash))
		return false;
	      return true;
	    }
	  // If stash exists and matches but has no info, it's an invalid/empty stash,
	  // so we should proceed to re-slurp (or return false if it's truly empty).
	  return false;
	}

      // Stash exists but doesn't match or is invalid for reuse, clean it up.
      // _bfd_dwarf2_cleanup_debug_info is expected to free the stash itself
      // and set *pinfo to NULL if it's the only reference.
      _bfd_dwarf2_cleanup_debug_info (abfd, pinfo);
      stash = NULL; // Reflect that it's cleaned up and will be reallocated
    }

  if (stash == NULL)
    {
      stash = (struct dwarf2_debug *) bfd_zalloc (abfd, sizeof (*stash));
      if (!stash)
	return false;
      *pinfo = stash;
      // bfd_zalloc ensures it's zeroed, no need for memset.
    }

  // --- Initial Stash Setup ---
  stash->orig_bfd_id = abfd->id;
  stash->debug_sections = debug_sections;
  stash->f.syms = active_symbols; // Initially set from parameter, might be updated later

  if (!save_section_vma (abfd, stash))
    {
      free_dwarf2_stash_contents(stash); // Clean up any partial state
      return false;
    }

  if (!allocate_stash_internal_resources(abfd, stash))
    {
      free_dwarf2_stash_contents(stash); // Helper cleans its own partial allocations
      return false;
    }

  // --- Resolve Debug BFD and Symbols ---
  // The 'symbols_param' passed to the function is an 'asymbol **'.
  // If we open a new debug_bfd, we might get new symbols.
  // The caller expects 'symbols_param' to be updated to point to the correct symbols.
  if (!resolve_debug_bfd_source(abfd, &active_debug_bfd, debug_sections, &active_symbols, &close_debug_bfd_on_cleanup))
    {
      free_dwarf2_stash_contents(stash);
      return false;
    }

  stash->f.bfd_ptr = active_debug_bfd;
  stash->f.syms = active_symbols; // Update stash with the potentially new symbols
  stash->close_on_cleanup = close_debug_bfd_on_cleanup;
  *symbols_param = active_symbols; // Update caller's symbols pointer

  // --- Section Placement ---
  if (do_place && !place_sections (abfd, stash))
    {
      free_dwarf2_stash_contents(stash);
      return false;
    }

  // --- Read Debug Info Sections ---
  if (!read_debug_info_sections(active_debug_bfd, debug_sections, active_symbols, stash))
    {
      free_dwarf2_stash_contents(stash);
      return false;
    }

  stash->f.info_ptr = stash->f.dwarf_info_buffer;
  // stash->f.dwarf_info_size is set by read_debug_info_sections
  return true;
}

// --- Helper Functions ---

// Frees contents of stash, but not the stash itself
static void free_dwarf2_stash_contents(struct dwarf2_debug *stash)
{
  if (stash == NULL)
    return;

  // Free hash tables
  if (stash->f.abbrev_offsets)
    {
      htab_delete (stash->f.abbrev_offsets);
      stash->f.abbrev_offsets = NULL;
    }

  if (stash->alt.abbrev_offsets)
    {
      htab_delete (stash->alt.abbrev_offsets);
      stash->alt.abbrev_offsets = NULL;
    }

  // Free trie roots (assuming alloc_trie_leaf implies free_trie_root is needed)
  if (stash->f.trie_root)
    {
      free_trie_root (stash->f.trie_root); // Assuming a function free_trie_root exists
      stash->f.trie_root = NULL;
    }

  if (stash->alt.trie_root)
    {
      free_trie_root (stash->alt.trie_root); // Assuming a function free_trie_root exists
      stash->alt.trie_root = NULL;
    }

  // Free debug info buffer
  if (stash->f.dwarf_info_buffer)
    {
      bfd_free (stash->f.dwarf_info_buffer);
      stash->f.dwarf_info_buffer = NULL;
      stash->f.dwarf_info_size = 0;
    }

  // Close debug BFD if we opened it
  if (stash->close_on_cleanup && stash->f.bfd_ptr)
    {
      bfd_close (stash->f.bfd_ptr);
    }
  stash->f.bfd_ptr = NULL;
  stash->close_on_cleanup = false;

  // Unset sections if they were saved
  unset_sections(stash);
}

// Allocates hash tables and trie roots for the stash
static bool allocate_stash_internal_resources(bfd *abfd, struct dwarf2_debug *stash)
{
  // Assume stash is already allocated and zeroed by bfd_zalloc
  // and checked by caller.

  stash->f.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev, del_abbrev, calloc, free);
  if (!stash->f.abbrev_offsets)
    return false;

  stash->alt.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev, del_abbrev, calloc, free);
  if (!stash->alt.abbrev_offsets)
    {
      htab_delete(stash->f.abbrev_offsets);
      stash->f.abbrev_offsets = NULL;
      return false;
    }

  stash->f.trie_root = alloc_trie_leaf (abfd);
  if (!stash->f.trie_root)
    {
      htab_delete(stash->f.abbrev_offsets);
      stash->f.abbrev_offsets = NULL;
      htab_delete(stash->alt.abbrev_offsets);
      stash->alt.abbrev_offsets = NULL;
      return false;
    }

  stash->alt.trie_root = alloc_trie_leaf (abfd);
  if (!stash->alt.trie_root)
    {
      htab_delete(stash->f.abbrev_offsets);
      stash->f.abbrev_offsets = NULL;
      htab_delete(stash->alt.abbrev_offsets);
      stash->alt.abbrev_offsets = NULL;
      free_trie_root(stash->f.trie_root);
      stash->f.trie_root = NULL;
      return false;
    }
  return true;
}

// Resolves the debug BFD source, potentially opening a new BFD or updating symbols.
static bool resolve_debug_bfd_source(bfd *abfd, bfd **p_debug_bfd,
                                     const struct dwarf_debug_section *debug_sections,
                                     asymbol ***p_symbols_out, bool *close_on_cleanup_out)
{
  bfd *current_debug_bfd = *p_debug_bfd;
  char *debug_filename = NULL;
  bool new_bfd_opened = false;
  asection *msec;

  // If initial debug_bfd_param was NULL, default to abfd for the initial search
  if (current_debug_bfd == NULL)
    current_debug_bfd = abfd;

  // Try to find debug info in the current_debug_bfd
  msec = find_debug_info (current_debug_bfd, debug_sections, NULL);

  if (msec == NULL && current_debug_bfd == abfd)
    {
      // No debug info found in original BFD, try following debuglink
      debug_filename = bfd_follow_build_id_debuglink (abfd, DEBUGDIR);
      if (debug_filename == NULL)
	debug_filename = bfd_follow_gnu_debuglink (abfd, DEBUGDIR);

      if (debug_filename == NULL)
	{
	  // No DWARF2 info, and no debuglink to follow.
	  return false;
	}

      bfd *linked_debug_bfd = bfd_openr (debug_filename, NULL);
      free (debug_filename); // Free the filename regardless of bfd_openr success
      debug_filename = NULL;

      if (linked_debug_bfd == NULL)
	return false;

      // Set BFD_DECOMPRESS to decompress debug sections.
      linked_debug_bfd->flags |= BFD_DECOMPRESS;

      // Check format and read symbols from the linked BFD
      if (!bfd_check_format (linked_debug_bfd, bfd_object)
	  || (msec = find_debug_info (linked_debug_bfd, debug_sections, NULL)) == NULL
	  || !bfd_generic_link_read_symbols (linked_debug_bfd))
	{
	  bfd_close (linked_debug_bfd);
	  return false;
	}

      current_debug_bfd = linked_debug_bfd;
      *p_symbols_out = bfd_get_outsymbols (current_debug_bfd);
      new_bfd_opened = true;
    }
  else if (msec != NULL && current_debug_bfd == abfd && *p_symbols_out == NULL)
    {
      // If current_debug_bfd is abfd, debug info found, but symbols_param was NULL.
      // Ensure symbols are loaded for 'abfd' if it contains debug info.
      if (!bfd_generic_link_read_symbols(current_debug_bfd))
	return false;
      *p_symbols_out = bfd_get_outsymbols(current_debug_bfd);
    }

  // If msec is NULL at this point, it means no debug info found even after following links.
  if (msec == NULL)
    {
      if (new_bfd_opened)
	bfd_close(current_debug_bfd); // Close the BFD we just opened if no info found
      return false;
    }

  *p_debug_bfd = current_debug_bfd;
  *close_on_cleanup_out = new_bfd_opened;
  return true;
}

// Reads the debug info sections into the stash.
static bool read_debug_info_sections(bfd *debug_bfd, const struct dwarf_debug_section *debug_sections,
                                     asymbol **symbols, struct dwarf2_debug *stash)
{
  bfd_size_type total_size;
  asection *msec;

  // First pass to find sections and determine if multiple exist
  msec = find_debug_info (debug_bfd, debug_sections, NULL);
  if (msec == NULL)
    {
      // No debug info section found at all. This should ideally be caught earlier.
      // Treat as empty debug info if no error has been set already.
      stash->f.dwarf_info_buffer = NULL;
      stash->f.dwarf_info_size = 0;
      return true;
    }

  if (! find_debug_info (debug_bfd, debug_sections, msec))
    {
      // Case 1: only one info section.
      total_size = bfd_get_section_limit_octets (debug_bfd, msec);
      if (!read_section (debug_bfd, &stash->debug_sections[debug_info], symbols,
                         0, &stash->f.dwarf_info_buffer, &total_size))
	return false;
      stash->f.dwarf_info_size = total_size;
    }
  else
    {
      // Case 2: multiple sections.
      bfd_size_type current_total_size = 0;
      for (asection *current_msec = find_debug_info (debug_bfd, debug_sections, NULL);
	   current_msec;
	   current_msec = find_debug_info (debug_bfd, debug_sections, current_msec))
	{
	  if (bfd_section_size_insane (debug_bfd, current_msec))
	    {
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, current_msec);
	  // PR25070: Check for overflow before adding
	  if (current_total_size > BFD_SIZE_TYPE_MAX - readsz) // BFD_SIZE_TYPE_MAX from BFD headers
	    {
	      bfd_set_error (bfd_error_no_memory);
	      return false;
	    }
	  current_total_size += readsz;
	}
      total_size = current_total_size; // Store the calculated total size

      if (total_size == 0)
	{
	  // No actual data to read, consider it successful (empty debug info)
	  stash->f.dwarf_info_buffer = NULL;
	  stash->f.dwarf_info_size = 0;
	  return true;
	}

      stash->f.dwarf_info_buffer = (bfd_byte *) bfd_malloc (total_size);
      if (stash->f.dwarf_info_buffer == NULL)
	{
	  bfd_set_error (bfd_error_no_memory);
	  return false;
	}

      bfd_size_type offset = 0;
      for (asection *current_msec = find_debug_info (debug_bfd, debug_sections, NULL);
	   current_msec;
	   current_msec = find_debug_info (debug_bfd, debug_sections, current_msec))
	{
	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, current_msec);
	  if (readsz == 0)
	    continue;

	  // Ensure we don't write beyond allocated buffer
	  if (offset > total_size || readsz > total_size - offset)
	    {
	      bfd_set_error (bfd_error_system_error); // Logic error in size calculation/iteration
	      return false;
	    }

	  if (!(bfd_simple_get_relocated_section_contents
		(debug_bfd, current_msec, stash->f.dwarf_info_buffer + offset,
		 symbols)))
	    return false;

	  offset += readsz;
	}
      stash->f.dwarf_info_size = total_size;
    }
  return true;
}

/* Parse the next DWARF2 compilation unit at FILE->INFO_PTR.  */

static struct comp_unit *
stash_comp_unit (struct dwarf2_debug *stash, struct dwarf2_debug_file *file)
{
  bfd_size_type cu_length;
  unsigned int offset_size;
  bfd_byte *cu_start_ptr = file->info_ptr;
  bfd_byte *dwarf_info_end = file->dwarf_info_buffer + file->dwarf_info_size;

  if (file->info_ptr >= dwarf_info_end)
    return NULL;

  cu_length = read_4_bytes (file->bfd_ptr, &file->info_ptr, dwarf_info_end);

  if (cu_length == 0xFFFFFFFFU)
    {
      offset_size = 8;
      cu_length = read_8_bytes (file->bfd_ptr, &file->info_ptr, dwarf_info_end);
    }
  else if (cu_length == 0U)
    {
      offset_size = 8;
      cu_length = read_4_bytes (file->bfd_ptr, &file->info_ptr, dwarf_info_end);
    }
  else
    {
      offset_size = 4;
    }

  bfd_size_type remaining_buffer_size = (bfd_size_type)(dwarf_info_end - file->info_ptr);
  if (cu_length == 0 || cu_length > remaining_buffer_size)
    {
      file->info_ptr = dwarf_info_end;
      return NULL;
    }

  struct comp_unit *new_comp_unit = parse_comp_unit (stash, file,
                                                     file->info_ptr, cu_length,
                                                     cu_start_ptr, offset_size);
  if (new_comp_unit == NULL)
    {
      file->info_ptr = dwarf_info_end;
      return NULL;
    }

  if (file->comp_unit_tree == NULL)
    {
      file->comp_unit_tree = splay_tree_new (splay_tree_compare_addr_range,
                                            splay_tree_free_addr_range, NULL);
      if (file->comp_unit_tree == NULL)
        {
          free_comp_unit (new_comp_unit);
          file->info_ptr = dwarf_info_end;
          return NULL;
        }
    }

  struct addr_range *range_key = (struct addr_range *) bfd_malloc (sizeof (struct addr_range));
  if (range_key == NULL)
    {
      free_comp_unit (new_comp_unit);
      file->info_ptr = dwarf_info_end;
      return NULL;
    }

  range_key->start = new_comp_unit->info_ptr_unit;
  range_key->end = new_comp_unit->end_ptr;

  if (range_key->end <= range_key->start)
    {
      bfd_free (range_key);
      free_comp_unit (new_comp_unit);
      file->info_ptr = dwarf_info_end;
      return NULL;
    }

  splay_tree_node existing_node = splay_tree_lookup (file->comp_unit_tree,
                                                    (splay_tree_key) range_key);
  if (existing_node != NULL)
    {
      bfd_free (range_key);
      free_comp_unit (new_comp_unit);
      file->info_ptr = dwarf_info_end;
      return NULL;
    }

  splay_tree_insert (file->comp_unit_tree, (splay_tree_key) range_key,
                     (splay_tree_value) new_comp_unit);

  new_comp_unit->next_unit = file->all_comp_units;
  if (file->all_comp_units)
    {
      file->all_comp_units->prev_unit = new_comp_unit;
    }
  else
    {
      file->last_comp_unit = new_comp_unit;
    }
  new_comp_unit->prev_unit = NULL;
  file->all_comp_units = new_comp_unit;

  if (new_comp_unit->arange.high == 0)
    {
      new_comp_unit->next_unit_without_ranges = file->all_comp_units_without_ranges;
      file->all_comp_units_without_ranges = new_comp_unit;
    }
  else
    {
      new_comp_unit->next_unit_without_ranges = NULL;
    }

  file->info_ptr += cu_length;

  return new_comp_unit;
}

/* Hash function for an asymbol.  */

static hashval_t
hash_asymbol (const void *sym)
{
  if (sym == NULL) {
    return 0;
  }

  const asymbol *asym = (const asymbol *)sym;

  if (asym->name == NULL) {
    return 0;
  }

  return htab_hash_string(asym->name);
}

/* Equality function for asymbols.  */

static int
eq_asymbol (const void *a, const void *b)
{
  const asymbol *sa = (const asymbol *)a;
  const asymbol *sb = (const asymbol *)b;

  if (sa == NULL) {
    return sb == NULL;
  }

  if (sb == NULL) {
    return 0;
  }

  if (sa->name == NULL) {
    return sb->name == NULL;
  }

  if (sb->name == NULL) {
    return 0;
  }

  return strcmp(sa->name, sb->name) == 0;
}

/* Scan the debug information in PINFO looking for a DW_TAG_subprogram
   abbrev with a DW_AT_low_pc attached to it.  Then lookup that same
   symbol in SYMBOLS and return the difference between the low_pc and
   the symbol's address.  Returns 0 if no suitable symbol could be found.  */

bfd_signed_vma
_bfd_dwarf2_find_symbol_bias (asymbol ** symbols, void ** pinfo)
{
  struct dwarf2_debug *stash = (struct dwarf2_debug *) *pinfo;
  htab_t sym_hash = NULL;
  bfd_signed_vma result = 0;
  bool found_bias = false;

  if (stash == NULL || symbols == NULL)
    return 0;

  sym_hash = htab_create_alloc (10, hash_asymbol, eq_asymbol,
				NULL, xcalloc, free);

  for (asymbol **psym = symbols; *psym != NULL; psym++)
    {
      asymbol *sym_entry = *psym;

      if ((sym_entry->flags & BSF_FUNCTION) && sym_entry->section != NULL)
	{
	  *(asymbol **)htab_find_slot (sym_hash, sym_entry, INSERT) = sym_entry;
	}
    }

  for (struct comp_unit *unit = stash->f.all_comp_units; unit != NULL; unit = unit->next_unit)
    {
      comp_unit_maybe_decode_line_info (unit);

      for (struct funcinfo *func = unit->function_table; func != NULL; func = func->prev_func)
	{
	  if (func->name != NULL && func->arange.low != 0)
	    {
	      asymbol search_sym;
	      search_sym.name = func->name;

	      asymbol *matched_sym = (asymbol *)htab_find (sym_hash, &search_sym);
	      if (matched_sym != NULL)
		{
		  result = func->arange.low - (matched_sym->value + matched_sym->section->vma);
		  found_bias = true;
		  break;
		}
	    }
	}

      if (found_bias)
	{
	  break;
	}
    }

  if (sym_hash != NULL)
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

#include "bfd.h"
#include "libbfd.h"
#include "dwarf2.h"

#ifndef __cplusplus
#ifndef bool
#define bool int
#endif
#ifndef true
#define true 1
#endif
#ifndef false
#define false 0
#endif
#endif

/* Forward declarations for helper functions */
static bool handle_alt_bfd_initialization(bfd *abfd, const char *alt_filename, struct dwarf2_debug *stash);
static void determine_search_parameters(bfd *abfd, asymbol **symbols_in, asymbol *symbol_param, asection *section, bfd_vma offset_in, bfd_vma *addr_out, asymbol **symbol_out, bool *do_line_out);
static int search_comp_units_for_line(bfd *abfd, struct dwarf2_debug *stash, asymbol *symbol_to_find, bfd_vma addr, const char **filename_ptr, unsigned int *linenumber_ptr);
static int search_comp_units_for_nearest_line(struct dwarf2_debug *stash, bfd_vma addr, const char **filename_ptr, struct funcinfo **function_out, unsigned int *linenumber_ptr, unsigned int *discriminator_ptr);
static int resolve_function_name(bfd *abfd, struct dwarf2_debug *stash, asymbol **symbols_in, asection *section, bfd_vma offset_param, const char **filename_ptr, const char **functionname_ptr, struct funcinfo *function_info, int current_found_status);

/* Helper function implementations */

static bool
handle_alt_bfd_initialization(bfd *abfd ATTRIBUTE_UNUSED, const char *alt_filename, struct dwarf2_debug *stash)
{
  bfd *alt_bfd = bfd_openr (alt_filename, NULL);
  if (alt_bfd == NULL)
    {
      /* bfd_openr will have set the bfd_error.  */
      return false;
    }
  if (!bfd_check_format (alt_bfd, bfd_object))
    {
      bfd_set_error (bfd_error_wrong_format);
      bfd_close (alt_bfd);
      return false;
    }
  stash->alt.bfd_ptr = alt_bfd;
  return true;
}

static void
determine_search_parameters(bfd *abfd, asymbol **symbols_in, asymbol *symbol_param, asection *section, bfd_vma offset_in, bfd_vma *addr_out, asymbol **symbol_out, bool *do_line_out)
{
  *symbol_out = symbol_param;

  if (*do_line_out)
    {
      /* If looking by symbol, section and offset are implicitly from symbol. */
      *addr_out = symbol_param->value;
    }
  else
    {
      *addr_out = offset_in;

      /* If we have no SYMBOL but the section we're looking at is not a
	 code section, then take a look through the list of symbols to see
	 if we have a symbol at the address we're looking for.  If we do
	 then use this to look up line information.  This will allow us to
	 give file and line results for data symbols.  We exclude code
	 symbols here, if we look up a function symbol and then look up the
	 line information we'll actually return the line number for the
	 opening '{' rather than the function definition line.  This is
	 because looking up by symbol uses the line table, in which the
	 first line for a function is usually the opening '{', while
	 looking up the function by section + offset uses the
	 DW_AT_decl_line from the function DW_TAG_subprogram for the line,
	 which will be the line of the function name.  */
      if (symbols_in != NULL && (section->flags & SEC_CODE) == 0)
	{
	  asymbol **tmp;
	  for (tmp = symbols_in; (*tmp) != NULL; ++tmp)
	    if ((*tmp)->the_bfd == abfd
		&& (*tmp)->section == section
		&& (*tmp)->value == offset_in
		&& (((*tmp)->flags & BSF_SECTION_SYM) == 0))
	      {
		*symbol_out = *tmp;
		*do_line_out = true;
		/* For local symbols, keep going in the hope we find a
		   global.  */
		if (((*symbol_out)->flags & BSF_GLOBAL) != 0)
		  break;
	      }
	}
    }
}

static int
search_comp_units_for_line(bfd *abfd, struct dwarf2_debug *stash, asymbol *symbol_to_find, bfd_vma addr, const char **filename_ptr, unsigned int *linenumber_ptr)
{
  struct comp_unit *each;

  /* The info hash tables use quite a bit of memory.  We may not want to
     always use them.  We use some heuristics to decide if and when to
     turn it on.  */
  if (stash->info_hash_status == STASH_INFO_HASH_OFF)
    stash_maybe_enable_info_hash_tables (abfd, stash);

  /* Keep info hash table up to date if they are available.  Note that we
     may disable the hash tables if there is any error duing update.  */
  if (stash->info_hash_status == STASH_INFO_HASH_ON)
    stash_maybe_update_info_hash_tables (stash);

  if (stash->info_hash_status == STASH_INFO_HASH_ON)
    {
      if (stash_find_line_fast (stash, symbol_to_find, addr,
                                filename_ptr, linenumber_ptr))
        return true;
    }

  /* Check the previously read comp. units first.  */
  for (each = stash->f.all_comp_units; each; each = each->next_unit)
    if (((symbol_to_find->flags & BSF_FUNCTION) == 0
         || comp_unit_may_contain_address (each, addr))
        && comp_unit_find_line (each, symbol_to_find, addr, filename_ptr,
                                 linenumber_ptr))
      {
        return true;
      }

  /* Read each remaining comp. units checking each as they are read.  */
  while ((each = stash_comp_unit (stash, &stash->f)) != NULL)
    {
      /* DW_AT_low_pc and DW_AT_high_pc are optional for
	 compilation units.  If we don't have them (i.e.,
	 unit->high == 0), we need to consult the line info table
	 to see if a compilation unit contains the given
	 address.  */
      if (((symbol_to_find->flags & BSF_FUNCTION) == 0
           || comp_unit_may_contain_address (each, addr))
          && comp_unit_find_line (each, symbol_to_find, addr,
                                  filename_ptr, linenumber_ptr))
        return true;
    }

  return false;
}

static int
search_comp_units_for_nearest_line(struct dwarf2_debug *stash, bfd_vma addr, const char **filename_ptr, struct funcinfo **function_out, unsigned int *linenumber_ptr, unsigned int *discriminator_ptr)
{
  struct trie_node *trie = stash->f.trie_root;
  unsigned int bits = VMA_BITS - 8;
  struct comp_unit *each;
  struct comp_unit **prev_each;

  /* Traverse interior nodes until we get to a leaf.  */
  while (trie && trie->num_room_in_leaf == 0)
    {
      int ch = (addr >> bits) & 0xff;
      trie = ((struct trie_interior *) trie)->children[ch];
      bits -= 8;
    }

  if (trie)
    {
      const struct trie_leaf *leaf = (const struct trie_leaf *) trie;
      unsigned int i;

      for (i = 0; i < leaf->num_stored_in_leaf; ++i)
	leaf->ranges[i].unit->mark = false;

      for (i = 0; i < leaf->num_stored_in_leaf; ++i)
	{
	  struct comp_unit *unit = leaf->ranges[i].unit;
	  if (unit->mark
	      || addr < leaf->ranges[i].low_pc
	      || addr >= leaf->ranges[i].high_pc)
	    continue;
	  unit->mark = true;

	  if (comp_unit_find_nearest_line (unit, addr,
						 filename_ptr,
						 function_out,
						 linenumber_ptr,
						 discriminator_ptr))
	    return true;
	}
    }

  /* Also scan through all compilation units without any ranges,
     taking them out of the list if they have acquired any since
     last time.  */
  prev_each = &stash->f.all_comp_units_without_ranges;
  each = *prev_each;
  while (each)
    {
      if (each->arange.high != 0)
	{
	  /* This unit now has ranges, remove it from this list. */
	  *prev_each = each->next_unit_without_ranges;
	  each = each->next_unit_without_ranges;
	  continue;
	}

      if (comp_unit_find_nearest_line (each, addr,
					   filename_ptr,
					   function_out,
					   linenumber_ptr,
					   discriminator_ptr))
	return true;
      
      prev_each = &each->next_unit_without_ranges;
      each = each->next_unit_without_ranges;
    }

  /* Read each remaining comp. units checking each as they are read.  */
  while ((each = stash_comp_unit (stash, &stash->f)) != NULL)
    {
      if (comp_unit_may_contain_address (each, addr)
          && comp_unit_find_nearest_line (each, addr,
                                         filename_ptr,
                                         function_out,
                                         linenumber_ptr,
                                         discriminator_ptr))
        return true;
    }

  return false;
}

static int
resolve_function_name(bfd *abfd, struct dwarf2_debug *stash, asymbol **symbols_in, asection *section, bfd_vma offset_param, const char **filename_ptr, const char **functionname_ptr, struct funcinfo *function_info, int current_found_status)
{
  if (function_info && function_info->is_linkage)
    {
      *functionname_ptr = function_info->name;
      if (!current_found_status)
        current_found_status = 2; /* Found function name via DWARF linkage */
    }
  else if (!*functionname_ptr || (function_info && !function_info->is_linkage))
    {
      asymbol *fun;
      asymbol **syms = symbols_in;
      asection *sec = section;

      _bfd_dwarf2_stash_syms (stash, abfd, &sec, &syms);
      fun = _bfd_elf_find_function (abfd, syms, sec, offset_param,
				    *filename_ptr ? NULL : filename_ptr,
				    functionname_ptr);

      if (!current_found_status && fun != NULL)
	current_found_status = 2; /* Found function name via ELF symbols */

      if (function_info && !function_info->is_linkage)
	{
	  bfd_vma sec_vma = section->vma;
	  if (section->output_section != NULL)
	    sec_vma = section->output_section->vma + section->output_offset;

	  if (fun == NULL)
	    *functionname_ptr = function_info->name;
	  else if (fun->value + sec_vma == function_info->arange.low)
	    function_info->name = *functionname_ptr;

	  /* Even if we didn't find a linkage name, say that we have
	     to stop a repeated search of symbols.  */
	  function_info->is_linkage = true;
	}
    }
  return current_found_status;
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
  struct funcinfo *function = NULL; /* Function info for DW_TAG_subprogram */
  bfd_vma search_addr;
  bool do_line;
  asymbol *primary_symbol_for_search = symbol; /* Symbol used for line table lookup */
  asection *effective_section = section; /* Section to use for address calculation */

  /* Initialize output pointers to NULL/zero */
  *filename_ptr = NULL;
  if (functionname_ptr != NULL)
    *functionname_ptr = NULL;
  *linenumber_ptr = 0;
  if (discriminator_ptr)
    *discriminator_ptr = 0;

  /* Slurp debug info. This must succeed. */
  if (! _bfd_dwarf2_slurp_debug_info (abfd, NULL, debug_sections,
				      symbols, pinfo,
				      (abfd->flags & (EXEC_P | DYNAMIC)) == 0))
    return false;

  stash = (struct dwarf2_debug *) *pinfo;

  /* A null info_ptr indicates that there is no dwarf2 info
     (or that an error occurred while setting up the stash).  */
  if (! stash->f.info_ptr)
    return false;

  /* Handle alternate BFD initialization if requested */
  if (stash->alt.bfd_ptr == NULL && alt_filename != NULL)
    {
      if (!handle_alt_bfd_initialization(abfd, alt_filename, stash))
	return false;
    }

  /* Determine the initial search mode (by symbol or by address) and validate inputs. */
  do_line = (symbol != NULL);

  if (do_line)
    {
      BFD_ASSERT (section == NULL && offset == 0);
      /* functionname_ptr is implicitly NULL here if only line info by symbol is sought */
      effective_section = bfd_asymbol_section (symbol);
    }
  else
    {
      BFD_ASSERT (section != NULL);
      /* functionname_ptr must be non-NULL if searching by address to find function */
      BFD_ASSERT (functionname_ptr != NULL);
    }

  /* Refine search parameters: search_addr, primary_symbol_for_search, and do_line.
     This handles the case of finding a data symbol at an address. */
  determine_search_parameters(abfd, symbols, symbol, effective_section, offset, &search_addr, &primary_symbol_for_search, &do_line);

  /* If a symbol was found or provided, ensure effective_section is consistent */
  if (primary_symbol_for_search != NULL)
    effective_section = bfd_asymbol_section (primary_symbol_for_search);

  /* Adjust search address based on section properties (output vs input) */
  if (effective_section->output_section)
    search_addr += effective_section->output_section->vma + effective_section->output_offset;
  else
    search_addr += effective_section->vma;

  stash->inliner_chain = NULL;
  int found_status = false;

  /* Perform the main search based on whether line info is for a specific symbol or nearest address */
  if (do_line)
    {
      found_status = search_comp_units_for_line(abfd, stash, primary_symbol_for_search, search_addr, filename_ptr, linenumber_ptr);
    }
  else
    {
      found_status = search_comp_units_for_nearest_line(stash, search_addr, filename_ptr, &function, linenumber_ptr, discriminator_ptr);
    }

  /* Resolve function name if requested */
  if (functionname_ptr != NULL)
    {
      found_status = resolve_function_name(abfd, stash, symbols, effective_section, offset, filename_ptr, functionname_ptr, function, found_status);
    }

  unset_sections (stash);

  return found_status;
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
  if (stash == NULL)
    {
      return false;
    }

  func = stash->inliner_chain;
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

static void
cleanup_line_table_members (struct line_table *lt)
{
  if (lt == NULL)
    return;
  free (lt->files);
  lt->files = NULL;
  free (lt->dirs);
  lt->dirs = NULL;
}

static void
cleanup_funcinfo_list (struct funcinfo *list_head)
{
  struct funcinfo *current = list_head;
  while (current)
    {
      struct funcinfo *temp = current;
      free (temp->file);
      temp->file = NULL;
      free (temp->caller_file);
      temp->caller_file = NULL;
      current = current->prev_func;
      free (temp);
    }
}

static void
cleanup_varinfo_list (struct varinfo *list_head)
{
  struct varinfo *current = list_head;
  while (current)
    {
      struct varinfo *temp = current;
      free (temp->file);
      temp->file = NULL;
      current = current->prev_var;
      free (temp);
    }
}

static void
cleanup_comp_unit_data (struct comp_unit *unit,
                        struct dwarf2_debug_file *parent_file)
{
  if (unit == NULL)
    return;

  if (unit->line_table != NULL && unit->line_table != parent_file->line_table)
    {
      cleanup_line_table_members (unit->line_table);
    }

  free (unit->lookup_funcinfo_table);
  unit->lookup_funcinfo_table = NULL;

  cleanup_funcinfo_list (unit->function_table);
  unit->function_table = NULL;

  cleanup_varinfo_list (unit->variable_table);
  unit->variable_table = NULL;
}

static void
cleanup_all_comp_units (struct comp_unit *list_head,
                        struct dwarf2_debug_file *parent_file)
{
  struct comp_unit *current = list_head;
  while (current)
    {
      struct comp_unit *temp = current;
      cleanup_comp_unit_data (temp, parent_file);
      current = current->next_unit;
      free (temp);
    }
}

static void
cleanup_dwarf2_debug_file (struct dwarf2_debug_file *file_ptr)
{
  if (file_ptr == NULL)
    return;

  cleanup_all_comp_units (file_ptr->all_comp_units, file_ptr);
  file_ptr->all_comp_units = NULL;

  if (file_ptr->line_table != NULL)
    {
      cleanup_line_table_members (file_ptr->line_table);
    }

  if (file_ptr->abbrev_offsets != NULL)
    {
      htab_delete (file_ptr->abbrev_offsets);
      file_ptr->abbrev_offsets = NULL;
    }

  if (file_ptr->comp_unit_tree != NULL)
    {
      splay_tree_delete (file_ptr->comp_unit_tree);
      file_ptr->comp_unit_tree = NULL;
    }

  free (file_ptr->dwarf_line_str_buffer);
  file_ptr->dwarf_line_str_buffer = NULL;
  free (file_ptr->dwarf_str_buffer);
  file_ptr->dwarf_str_buffer = NULL;
  free (file_ptr->dwarf_ranges_buffer);
  file_ptr->dwarf_ranges_buffer = NULL;
  free (file_ptr->dwarf_rnglists_buffer);
  file_ptr->dwarf_rnglists_buffer = NULL;
  free (file_ptr->dwarf_line_buffer);
  file_ptr->dwarf_line_buffer = NULL;
  free (file_ptr->dwarf_abbrev_buffer);
  file_ptr->dwarf_abbrev_buffer = NULL;
  free (file_ptr->dwarf_info_buffer);
  file_ptr->dwarf_info_buffer = NULL;
  free (file_ptr->dwarf_addr_buffer);
  file_ptr->dwarf_addr_buffer = NULL;
  free (file_ptr->dwarf_str_offsets_buffer);
  file_ptr->dwarf_str_offsets_buffer = NULL;
}

void
_bfd_dwarf2_cleanup_debug_info (bfd *abfd, void **pinfo)
{
  struct dwarf2_debug *stash;

  if (pinfo == NULL || *pinfo == NULL)
    return;

  stash = (struct dwarf2_debug *) *pinfo;

  if (stash->varinfo_hash_table != NULL)
    {
      bfd_hash_table_free (&stash->varinfo_hash_table->base);
      stash->varinfo_hash_table = NULL;
    }
  if (stash->funcinfo_hash_table != NULL)
    {
      bfd_hash_table_free (&stash->funcinfo_hash_table->base);
      stash->funcinfo_hash_table = NULL;
    }

  cleanup_dwarf2_debug_file (&stash->f);
  cleanup_dwarf2_debug_file (&stash->alt);

  free (stash->sec_vma);
  stash->sec_vma = NULL;
  free (stash->adjusted_sections);
  stash->adjusted_sections = NULL;

  if (stash->close_on_cleanup && stash->f.bfd_ptr != NULL)
    {
      bfd_close (stash->f.bfd_ptr);
      stash->f.bfd_ptr = NULL;
    }
  if (stash->alt.bfd_ptr != NULL)
    {
      bfd_close (stash->alt.bfd_ptr);
      stash->alt.bfd_ptr = NULL;
    }

  *pinfo = NULL;
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
  /* If the new symbol starts after the desired offset, it cannot be a better fit. */
  if (code_off > offset) {
    return false;
  }

  /* Primary comparison: Prefer symbols that start later (closer to offset). */
  /* Both code_off and cache->code_off are guaranteed to be <= offset at this point. */
  if (code_off > cache->code_off) {
    return true;
  }
  if (code_off < cache->code_off) {
    return false;
  }

  /* At this point, code_off == cache->code_off.
     We now compare based on coverage and other tie-breaking rules. */

  const bfd_vma cache_end_offset = cache->code_off + cache->code_size;
  const bfd_vma sym_end_offset   = code_off + code_size;

  const bool cache_covers_offset = (cache_end_offset > offset);
  const bool sym_covers_offset   = (sym_end_offset > offset);

  /* If one symbol covers the offset and the other does not, prefer the one that covers it. */
  if (sym_covers_offset && !cache_covers_offset) {
    return true;
  }
  if (!sym_covers_offset && cache_covers_offset) {
    return false;
  }

  /* If neither symbol covers the offset (or both do not), prefer the one that extends further. */
  if (!sym_covers_offset && !cache_covers_offset) {
    return code_size > cache->code_size; /* Prefer greater size to get closer to OFFSET */
  }

  /* At this point, both symbols start at the same offset and both cover the desired offset.
     Apply tie-breaking rules. */

  /* Tie-breaker 1: Prefer functions over non-functions. */
  const bool cache_is_function = (cache->func->flags & BSF_FUNCTION) != 0;
  const bool sym_is_function   = (sym->flags & BSF_FUNCTION) != 0;

  if (sym_is_function && !cache_is_function) {
    return true;
  }
  if (!sym_is_function && cache_is_function) {
    return false;
  }

  /* Tie-breaker 2: Prefer typed symbols over notyped.
     Note: This cast implies that asymbol* can be safely cast to elf_symbol_type*.
     This is typical in BFD/ELF contexts where `asymbol` is a base type. */
  const int cache_type = ELF_ST_TYPE (((elf_symbol_type *) cache->func)->internal_elf_sym.st_info);
  const int sym_type   = ELF_ST_TYPE (((elf_symbol_type *) sym)->internal_elf_sym.st_info);

  const bool cache_is_typed = (cache_type != STT_NOTYPE);
  const bool sym_is_typed   = (sym_type != STT_NOTYPE);

  if (sym_is_typed && !cache_is_typed) {
    return true;
  }
  if (!sym_is_typed && cache_is_typed) {
    return false;
  }

  /* Tie-breaker 3: Otherwise, prefer whichever symbol covers a smaller area. */
  return code_size < cache->code_size;
}

/* Find the function to a particular section and offset,
   for error reporting.  */

static void
elf_bfd_reset_find_function_cache(elf_find_function_cache *cache, asection *section)
{
  cache->filename = NULL;
  cache->func = NULL;
  cache->code_size = 0;
  cache->code_off = 0;
  cache->last_section = section;
}

asymbol *
_bfd_elf_find_function (bfd *abfd,
			asymbol **symbols,
			asection *section,
			bfd_vma offset,
			const char **filename_ptr,
			const char **functionname_ptr)
{
  if (abfd == NULL || symbols == NULL)
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
      asymbol *file_symbol = NULL;
      enum { nothing_seen, symbol_seen, file_after_symbol_seen } state;
      const struct elf_backend_data *bed = get_elf_backend_data (abfd);

      elf_bfd_reset_find_function_cache(cache, section);
      state = nothing_seen;

      for (asymbol **p = symbols; *p != NULL; p++)
	{
	  asymbol *sym = *p;
	  bfd_vma code_off;
	  bfd_size_type size;

	  if ((sym->flags & BSF_FILE) != 0)
	    {
	      file_symbol = sym;
	      if (state == symbol_seen)
		state = file_after_symbol_seen;
	      continue;
	    }

	  if (state == nothing_seen)
	    state = symbol_seen;

	  size = bed->maybe_function_sym (sym, section, &code_off);

	  if (size == 0)
	    continue;

	  if (better_fit (cache, sym, code_off, size, offset))
	    {
	      cache->func = sym;
	      cache->code_size = size;
	      cache->code_off = code_off;
	      cache->filename = NULL;

	      if (file_symbol != NULL
		  && ((sym->flags & BSF_LOCAL) != 0
		      || state != file_after_symbol_seen))
		cache->filename = bfd_asymbol_name (file_symbol);
	    }
	  else if (cache->func != NULL
		   && code_off > offset
		   && code_off > cache->code_off
		   && code_off < cache->code_off + cache->code_size)
	    {
	      cache->code_size = code_off - cache->code_off;
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
