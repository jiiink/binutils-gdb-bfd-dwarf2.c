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
  size_t header_size = sizeof (*leaf);
  size_t elem_size = sizeof (leaf->ranges[0]);
  size_t count = (size_t) TRIE_LEAF_SIZE;
  size_t total_size;

  if (abfd == NULL)
    return NULL;

  if (elem_size != 0 && count > (SIZE_MAX - header_size) / elem_size)
    return NULL;

  total_size = header_size + count * elem_size;

  leaf = bfd_zalloc (abfd, total_size);
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
addr_range_intersects (const struct addr_range *r1, const struct addr_range *r2)
{
  return (r1->start < r2->end) && (r2->start < r1->end);
}

/* Compare function for splay tree of addr_ranges.  */

static int
splay_tree_compare_addr_range(splay_tree_key xa, splay_tree_key xb)
{
  const struct addr_range *r1 = (const struct addr_range *) xa;
  const struct addr_range *r2 = (const struct addr_range *) xb;

  if (r1 == r2)
    return 0;

  if (addr_range_intersects(r1, r2) || addr_range_intersects(r2, r1))
    return 0;

  if (r1->end <= r2->start)
    return -1;

  return 1;
}

/* Splay tree release function for keys (addr_range).  */

static void
splay_tree_free_addr_range (splay_tree_key key)
{
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
info_hash_table_newfunc(struct bfd_hash_entry *entry,
                        struct bfd_hash_table *table,
                        const char *string)
{
    struct info_hash_entry *info_entry = (struct info_hash_entry *) entry;
    struct bfd_hash_entry *base_entry;

    if (info_entry == NULL) {
        info_entry = (struct info_hash_entry *) bfd_hash_allocate(table, sizeof(*info_entry));
        if (info_entry == NULL) {
            return NULL;
        }
    }

    base_entry = bfd_hash_newfunc((struct bfd_hash_entry *) info_entry, table, string);
    if (base_entry == NULL) {
        return NULL;
    }

    info_entry = (struct info_hash_entry *) base_entry;
    info_entry->head = NULL;

    return base_entry;
}

/* Function to create a new info hash table.  It returns a pointer to the
   newly created table or NULL if there is any error.  We need abfd
   solely for memory allocation.  */

static struct info_hash_table *
create_info_hash_table(bfd *abfd)
{
  struct info_hash_table *hash_table;

  if (abfd == NULL)
    return NULL;

  hash_table = bfd_alloc(abfd, sizeof *hash_table);
  if (hash_table == NULL)
    return NULL;

  if (!bfd_hash_table_init(&hash_table->base, info_hash_table_newfunc,
                           sizeof(struct info_hash_entry)))
    {
      bfd_release(abfd, hash_table);
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

  if (hash_table == NULL || key == NULL)
    return false;

  entry = (struct info_hash_entry *) bfd_hash_lookup (&hash_table->base,
						      key, true, copy_p);
  if (entry == NULL)
    return false;

  node = bfd_hash_allocate (&hash_table->base, sizeof (*node));
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
lookup_info_hash_table(struct info_hash_table *hash_table, const char *key)
{
    struct info_hash_entry *entry;

    if (hash_table == NULL || key == NULL) {
        return NULL;
    }

    entry = (struct info_hash_entry *) bfd_hash_lookup(&hash_table->base, key, false, false);
    if (entry == NULL) {
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
  if (abfd == NULL || sec == NULL || section_buffer == NULL || section_size == NULL)
    {
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  const char *section_name = sec->uncompressed_name;
  bfd_byte *contents = *section_buffer;

  if (contents == NULL)
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
      *section_size = size;
      bfd_size_type alloc = size + 1;
      if (alloc <= size)
	{
	  bfd_set_error (bfd_error_no_memory);
	  return false;
	}

      contents = (bfd_byte *) bfd_malloc (alloc);
      if (contents == NULL)
	return false;

      bool ok;
      if (syms != NULL)
	ok = bfd_simple_get_relocated_section_contents (abfd, msec, contents,
							syms);
      else
	ok = bfd_get_section_contents (abfd, msec, contents, 0, *section_size);

      if (! ok)
	{
	  free (contents);
	  return false;
	}

      contents[*section_size] = 0;
      *section_buffer = contents;
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

static inline uint64_t
read_n_bytes(bfd *abfd, bfd_byte **ptr, bfd_byte *end, int n)
{
  if (ptr == NULL || *ptr == NULL || end == NULL || abfd == NULL)
    return 0;

  if (n <= 0)
    return 0;

  bfd_byte *buf = *ptr;
  size_t available = (buf <= end) ? (size_t)(end - buf) : 0u;
  size_t needed = (size_t)n;

  if (available < needed)
    {
      *ptr = end;
      return 0;
    }

  *ptr = buf + needed;

  unsigned int bits = (unsigned int)(needed * 8u);
  return bfd_get(bits, abfd, buf);
}

static unsigned int
read_1_byte(bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  return read_n_bytes(abfd, ptr, end, 1u);
}

static int
read_1_signed_byte(bfd *abfd ATTRIBUTE_UNUSED, bfd_byte **ptr, bfd_byte *end)
{
  if (ptr == NULL || end == NULL || *ptr == NULL)
    return 0;

  bfd_byte *cursor = *ptr;

  if (cursor >= end)
    {
      *ptr = end;
      return 0;
    }

  *ptr = cursor + 1;
  return bfd_get_signed_8(abfd, cursor);
}

static unsigned int
read_2_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  const unsigned int bytes_to_read = 2U;
  return read_n_bytes (abfd, ptr, end, bytes_to_read);
}

static unsigned int
read_3_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  const unsigned int b0 = read_1_byte (abfd, ptr, end) & 0xFFu;
  const unsigned int b1 = read_1_byte (abfd, ptr, end) & 0xFFu;
  const unsigned int b2 = read_1_byte (abfd, ptr, end) & 0xFFu;

  if (bfd_little_endian (abfd))
    return b2 | (b1 << 8) | (b0 << 16);

  return (b0 << 16) | (b1 << 8) | b2;
}

static unsigned int
read_4_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  const unsigned int bytes_to_read = 4U;
  return read_n_bytes (abfd, ptr, end, bytes_to_read);
}

static uint64_t
read_8_bytes (bfd *abfd, bfd_byte **ptr, bfd_byte *end)
{
  return read_n_bytes (abfd, ptr, end, sizeof (uint64_t));
}

static struct dwarf_block *
read_blk (bfd *abfd, bfd_byte **ptr, bfd_byte *end, size_t size)
{
  bfd_byte *buf;
  struct dwarf_block *block;
  size_t avail;

  if (abfd == NULL || ptr == NULL || *ptr == NULL || end == NULL)
    return NULL;

  buf = *ptr;
  block = bfd_alloc (abfd, sizeof *block);
  if (block == NULL)
    return NULL;

  if (end <= buf)
    {
      *ptr = end;
      block->data = NULL;
      block->size = 0;
      return block;
    }

  avail = (size_t) (end - buf);
  if (size > avail)
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
read_string(bfd_byte **ptr, bfd_byte *buf_end)
{
  if (ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  bfd_byte *buf = *ptr;
  bfd_byte *start = buf;

  while (buf < buf_end)
  {
    if (*buf == 0)
    {
      if (buf == start)
      {
        buf++;
        break;
      }
      *ptr = buf + 1;
      return (char *) start;
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
  size_t offset_size;
  ptrdiff_t diff;
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  char *str;

  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  offset_size = unit->offset_size;
  if (offset_size != 4 && offset_size != 8)
    {
      *ptr = buf_end;
      return NULL;
    }

  diff = buf_end - *ptr;
  if (diff < 0 || (size_t) diff < offset_size)
    {
      *ptr = buf_end;
      return NULL;
    }

  if (offset_size == 4)
    offset = read_4_bytes (unit->abfd, ptr, buf_end);
  else
    offset = read_8_bytes (unit->abfd, ptr, buf_end);

  stash = unit->stash;
  file = unit->file;
  if (stash == NULL || file == NULL)
    return NULL;

  if (! read_section (unit->abfd, &stash->debug_sections[debug_str],
		      file->syms, offset,
		      &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  if (file->dwarf_str_buffer == NULL)
    return NULL;

  if (offset >= (uint64_t) file->dwarf_str_size)
    return NULL;

  str = (char *) file->dwarf_str_buffer + (size_t) offset;
  if (*str == '\0')
    return NULL;

  return str;
}

/* Like read_indirect_string but from .debug_line_str section.  */

static char *
read_indirect_line_string(struct comp_unit *unit,
                          bfd_byte **ptr,
                          bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  bfd *abfd;
  size_t remaining;

  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  if (*ptr >= buf_end)
    {
      *ptr = buf_end;
      return NULL;
    }

  stash = unit->stash;
  file = unit->file;
  abfd = unit->abfd;

  remaining = (size_t) (buf_end - *ptr);
  if (unit->offset_size > remaining)
    {
      *ptr = buf_end;
      return NULL;
    }

  if (unit->offset_size == 4)
    offset = read_4_bytes(abfd, ptr, buf_end);
  else if (unit->offset_size == 8)
    offset = read_8_bytes(abfd, ptr, buf_end);
  else
    {
      *ptr = buf_end;
      return NULL;
    }

  if (stash == NULL || file == NULL)
    return NULL;

  if (!read_section(abfd, &stash->debug_sections[debug_line_str],
                    file->syms, offset,
                    &file->dwarf_line_str_buffer,
                    &file->dwarf_line_str_size))
    return NULL;

  if (file->dwarf_line_str_buffer == NULL
      || offset >= file->dwarf_line_str_size)
    return NULL;

  {
    bfd_byte *base = file->dwarf_line_str_buffer;
    char *str = (char *) (base + (size_t) offset);
    if (*str == '\0')
      return NULL;
    return str;
  }
}

/* Like read_indirect_string but uses a .debug_str located in
   an alternate file pointed to by the .gnu_debugaltlink section.
   Used to impement DW_FORM_GNU_strp_alt.  */

static char *
read_alt_indirect_string(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
  uint64_t offset;
  struct dwarf2_debug *stash;
  char *str;

  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL)
    return NULL;

  stash = unit->stash;

  {
    size_t available = (size_t) (buf_end - *ptr);
    if (unit->offset_size > available)
      {
        *ptr = buf_end;
        return NULL;
      }
  }

  if (unit->offset_size == 4)
    offset = read_4_bytes(unit->abfd, ptr, buf_end);
  else
    offset = read_8_bytes(unit->abfd, ptr, buf_end);

  if (stash == NULL)
    return NULL;

  if (stash->alt.bfd_ptr == NULL)
    {
      bfd *debug_bfd;
      char *debug_filename = bfd_follow_gnu_debugaltlink(unit->abfd, DEBUGDIR);
      if (debug_filename == NULL)
        return NULL;

      debug_bfd = bfd_openr(debug_filename, NULL);
      free(debug_filename);
      if (debug_bfd == NULL)
        return NULL;

      if (!bfd_check_format(debug_bfd, bfd_object))
        {
          bfd_close(debug_bfd);
          return NULL;
        }
      stash->alt.bfd_ptr = debug_bfd;
    }

  if (!read_section(stash->alt.bfd_ptr,
                    stash->debug_sections + debug_str_alt,
                    stash->alt.syms, offset,
                    &stash->alt.dwarf_str_buffer,
                    &stash->alt.dwarf_str_size))
    return NULL;

  if (offset >= (uint64_t) stash->alt.dwarf_str_size)
    return NULL;

  str = (char *) stash->alt.dwarf_str_buffer + offset;
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

  if (stash == NULL)
    return NULL;

  if (stash->alt.bfd_ptr == NULL)
    {
      char *debug_filename = bfd_follow_gnu_debugaltlink (unit->abfd, DEBUGDIR);
      bfd *debug_bfd;

      if (debug_filename == NULL)
        return NULL;

      debug_bfd = bfd_openr (debug_filename, NULL);
      free (debug_filename);
      if (debug_bfd == NULL)
        return NULL;

      if (! bfd_check_format (debug_bfd, bfd_object))
        {
          bfd_close (debug_bfd);
          return NULL;
        }

      stash->alt.bfd_ptr = debug_bfd;
    }

  if (! read_section (stash->alt.bfd_ptr,
                      stash->debug_sections + debug_info_alt,
                      stash->alt.syms,
                      offset,
                      &stash->alt.dwarf_info_buffer,
                      &stash->alt.dwarf_info_size))
    return NULL;

  if (stash->alt.dwarf_info_buffer == NULL)
    return NULL;

  {
    uint64_t size64 = (uint64_t) stash->alt.dwarf_info_size;
    if (offset >= size64)
      return NULL;

    return stash->alt.dwarf_info_buffer + offset;
  }
}

static uint64_t
read_address(struct comp_unit *unit, bfd_byte **ptr, bfd_byte *buf_end)
{
  if (unit == NULL || ptr == NULL || *ptr == NULL || buf_end == NULL || unit->abfd == NULL)
    {
      if (ptr != NULL && *ptr != NULL)
        *ptr = buf_end;
      return 0;
    }

  bfd_byte *buf = *ptr;

  if (buf_end < buf)
    {
      *ptr = buf_end;
      return 0;
    }

  size_t size = unit->addr_size;
  size_t avail = (size_t)(buf_end - buf);

  if (size > avail)
    {
      *ptr = buf_end;
      return 0;
    }

  int signed_vma = 0;
  if (bfd_get_flavour(unit->abfd) == bfd_target_elf_flavour)
    signed_vma = get_elf_backend_data(unit->abfd)->sign_extend_vma;

  uint64_t result;

  switch (size)
    {
    case 8:
      result = signed_vma ? (uint64_t) bfd_get_signed_64(unit->abfd, buf)
                          : bfd_get_64(unit->abfd, buf);
      break;
    case 4:
      result = signed_vma ? (uint64_t) bfd_get_signed_32(unit->abfd, buf)
                          : bfd_get_32(unit->abfd, buf);
      break;
    case 2:
      result = signed_vma ? (uint64_t) bfd_get_signed_16(unit->abfd, buf)
                          : bfd_get_16(unit->abfd, buf);
      break;
    default:
      abort();
    }

  *ptr = buf + size;
  return result;
}

/* Lookup an abbrev_info structure in the abbrev hash table.  */

static struct abbrev_info *
lookup_abbrev(unsigned int number, struct abbrev_info **abbrevs)
{
  if (abbrevs == NULL)
    return NULL;

  struct abbrev_info *abbrev = abbrevs[number % ABBREV_HASH_SIZE];
  for (; abbrev != NULL; abbrev = abbrev->next)
    {
      if (abbrev->number == number)
        return abbrev;
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
  if (p == NULL)
    return 0;

  const struct abbrev_offset_entry *ent = (const struct abbrev_offset_entry *) p;
  return (hashval_t) ent->offset;
}

static int eq_abbrev(const void *pa, const void *pb)
{
    if (pa == pb) {
        return 1;
    }
    if (pa == NULL || pb == NULL) {
        return 0;
    }

    const struct abbrev_offset_entry *a = (const struct abbrev_offset_entry *)pa;
    const struct abbrev_offset_entry *b = (const struct abbrev_offset_entry *)pb;

    return a->offset == b->offset;
}

static void
del_abbrev (void *p)
{
  if (p == NULL)
    return;

  struct abbrev_offset_entry *ent = p;
  struct abbrev_info **abbrevs = ent->abbrevs;
  size_t i;

  if (abbrevs != NULL)
    {
      for (i = 0; i < ABBREV_HASH_SIZE; i++)
        {
          struct abbrev_info *curr = abbrevs[i];
          while (curr != NULL)
            {
              struct abbrev_info *next = curr->next;
              free (curr->attrs);
              free (curr);
              curr = next;
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

static struct abbrev_info**
read_abbrevs (bfd *abfd, uint64_t offset, struct dwarf2_debug *stash,
	      struct dwarf2_debug_file *file)
{
  struct abbrev_info **abbrevs = NULL;
  bfd_byte *abbrev_ptr;
  bfd_byte *abbrev_end;
  struct abbrev_info *cur_abbrev;
  unsigned int abbrev_number, abbrev_name;
  unsigned int abbrev_form, hash_number;
  size_t amt;
  void **slot;
  struct abbrev_offset_entry ent = { offset, NULL };

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

  if (file->dwarf_abbrev_buffer == NULL || file->dwarf_abbrev_size == 0 || offset > file->dwarf_abbrev_size)
    return NULL;

  if (ABBREV_HASH_SIZE > SIZE_MAX / sizeof (*abbrevs))
    return NULL;

  amt = sizeof (*abbrevs) * ABBREV_HASH_SIZE;
  abbrevs = (struct abbrev_info **) bfd_malloc (amt);
  if (abbrevs == NULL)
    return NULL;
  memset (abbrevs, 0, amt);

  abbrev_ptr = file->dwarf_abbrev_buffer + offset;
  abbrev_end = file->dwarf_abbrev_buffer + file->dwarf_abbrev_size;
  abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);

  while (abbrev_number)
    {
      amt = sizeof (struct abbrev_info);
      cur_abbrev = (struct abbrev_info *) bfd_zalloc (abfd, amt);
      if (cur_abbrev == NULL)
	goto fail;

      cur_abbrev->number = abbrev_number;
      cur_abbrev->tag = (enum dwarf_tag)
	_bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
      cur_abbrev->has_children = read_1_byte (abfd, &abbrev_ptr, abbrev_end);

      for (;;)
	{
	  bfd_vma implicit_const = (bfd_vma) -1;

	  abbrev_name = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
	  abbrev_form = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
	  if (abbrev_form == DW_FORM_implicit_const)
	    implicit_const = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, true, abbrev_end);
	  if (abbrev_name == 0)
	    break;

	  if ((cur_abbrev->num_attrs % ATTR_ALLOC_CHUNK) == 0)
	    {
	      struct attr_abbrev *tmp;

	      if (cur_abbrev->num_attrs > SIZE_MAX / sizeof (struct attr_abbrev) - ATTR_ALLOC_CHUNK)
		goto fail;

	      amt = (cur_abbrev->num_attrs + ATTR_ALLOC_CHUNK) * sizeof (struct attr_abbrev);
	      tmp = (struct attr_abbrev *) bfd_realloc (cur_abbrev->attrs, amt);
	      if (tmp == NULL)
		goto fail;
	      cur_abbrev->attrs = tmp;
	    }

	  cur_abbrev->attrs[cur_abbrev->num_attrs].name
	    = (enum dwarf_attribute) abbrev_name;
	  cur_abbrev->attrs[cur_abbrev->num_attrs].form
	    = (enum dwarf_form) abbrev_form;
	  cur_abbrev->attrs[cur_abbrev->num_attrs].implicit_const
	    = implicit_const;
	  ++cur_abbrev->num_attrs;
	}

      hash_number = abbrev_number % ABBREV_HASH_SIZE;
      cur_abbrev->next = abbrevs[hash_number];
      abbrevs[hash_number] = cur_abbrev;

      if ((size_t) (abbrev_ptr - file->dwarf_abbrev_buffer) >= file->dwarf_abbrev_size)
	break;
      abbrev_number = _bfd_safe_read_leb128 (abfd, &abbrev_ptr, false, abbrev_end);
      if (lookup_abbrev (abbrev_number, abbrevs) != NULL)
	break;
    }

  *slot = bfd_malloc (sizeof ent);
  if (!*slot)
    goto fail;
  ent.abbrevs = abbrevs;
  memcpy (*slot, &ent, sizeof ent);
  return abbrevs;

 fail:
  if (abbrevs != NULL)
    {
      size_t i;

      for (i = 0; i < ABBREV_HASH_SIZE; i++)
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
  return NULL;
}

/* Returns true if the form is one which has a string value.  */

static bool
is_str_form (const struct attribute *attr)
{
  return attr != NULL &&
         (attr->form == DW_FORM_string ||
          attr->form == DW_FORM_strp ||
          attr->form == DW_FORM_strx ||
          attr->form == DW_FORM_strx1 ||
          attr->form == DW_FORM_strx2 ||
          attr->form == DW_FORM_strx3 ||
          attr->form == DW_FORM_strx4 ||
          attr->form == DW_FORM_line_strp ||
          attr->form == DW_FORM_GNU_strp_alt);
}

/* Returns true if the form is one which has an integer value.  */

static bool
is_int_form (const struct attribute *attr)
{
  if (attr == NULL)
    return false;

  static const int forms[] = {
    DW_FORM_addr,
    DW_FORM_data2,
    DW_FORM_data4,
    DW_FORM_data8,
    DW_FORM_data1,
    DW_FORM_flag,
    DW_FORM_sdata,
    DW_FORM_udata,
    DW_FORM_ref_addr,
    DW_FORM_ref1,
    DW_FORM_ref2,
    DW_FORM_ref4,
    DW_FORM_ref8,
    DW_FORM_ref_udata,
    DW_FORM_sec_offset,
    DW_FORM_flag_present,
    DW_FORM_ref_sig8,
    DW_FORM_addrx,
    DW_FORM_implicit_const,
    DW_FORM_addrx1,
    DW_FORM_addrx2,
    DW_FORM_addrx3,
    DW_FORM_addrx4,
    DW_FORM_GNU_ref_alt
  };

  const int form = (int) attr->form;
  for (size_t i = 0; i < sizeof forms / sizeof forms[0]; ++i)
    {
      if (form == forms[i])
        return true;
    }
  return false;
}

/* Returns true if the form is strx[1-4].  */

static inline bool
is_strx_form(enum dwarf_form form)
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
is_addrx_form(enum dwarf_form form)
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
  bfd *abfd = unit->abfd;
  size_t addr_size = (size_t) unit->addr_size;
  size_t offset;
  size_t base;
  size_t size;
  bfd_byte *info_ptr;

  if (!read_section (abfd, &stash->debug_sections[debug_addr],
                     file->syms, 0,
                     &file->dwarf_addr_buffer, &file->dwarf_addr_size))
    return 0;

  if (file->dwarf_addr_buffer == NULL)
    return 0;

  if (addr_size != 4 && addr_size != 8)
    return 0;

  if (_bfd_mul_overflow ((size_t) idx, addr_size, &offset))
    return 0;

  base = unit->dwarf_addr_offset;
  size = file->dwarf_addr_size;

  offset += base;
  if (offset < base || offset > size || size - offset < addr_size)
    return 0;

  info_ptr = file->dwarf_addr_buffer + offset;

  if (addr_size == 4)
    return bfd_get_32 (abfd, info_ptr);
  return bfd_get_64 (abfd, info_ptr);
}

/* Returns the string using DW_AT_str_offsets_base.
   Used to implement DW_FORM_strx*.  */
static const char *
read_indexed_string(uint64_t idx, struct comp_unit *unit)
{
  if (unit == NULL || unit->stash == NULL || unit->file == NULL)
    return NULL;

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;
  size_t off_size = unit->offset_size;
  const bfd_byte *info_ptr;
  uint64_t str_offset;
  size_t offset;

  if (off_size != 4 && off_size != 8)
    return NULL;

  if (!read_section(unit->abfd, &stash->debug_sections[debug_str],
                    file->syms, 0,
                    &file->dwarf_str_buffer, &file->dwarf_str_size))
    return NULL;

  if (!read_section(unit->abfd, &stash->debug_sections[debug_str_offsets],
                    file->syms, 0,
                    &file->dwarf_str_offsets_buffer,
                    &file->dwarf_str_offsets_size))
    return NULL;

  if (_bfd_mul_overflow(idx, off_size, &offset))
    return NULL;

  offset += unit->dwarf_str_offset;
  if (offset < unit->dwarf_str_offset
      || offset > file->dwarf_str_offsets_size
      || file->dwarf_str_offsets_size - offset < off_size)
    return NULL;

  info_ptr = file->dwarf_str_offsets_buffer + offset;

  if (off_size == 4)
    str_offset = bfd_get_32(unit->abfd, info_ptr);
  else
    str_offset = bfd_get_64(unit->abfd, info_ptr);

  if (str_offset >= file->dwarf_str_size)
    return NULL;

  return (const char *) file->dwarf_str_buffer + (size_t) str_offset;
}

/* Read and fill in the value of attribute ATTR as described by FORM.
   Read data starting from INFO_PTR, but never at or beyond INFO_PTR_END.
   Returns an updated INFO_PTR taking into account the amount of data read.  */

static inline bfd_vma read_offset_sized_value(struct comp_unit *unit, bfd_byte **pinfo, bfd_byte *end)
{
  return unit->offset_size == 4
         ? read_4_bytes(unit->abfd, pinfo, end)
         : read_8_bytes(unit->abfd, pinfo, end);
}

static inline bfd_vma maybe_read_indexed_address(bfd_vma val, struct comp_unit *unit)
{
  return unit->dwarf_addr_offset != 0 ? read_indexed_address(val, unit) : val;
}

static inline int set_block_attr_from_size(struct attribute *attr, bfd *abfd, bfd_byte **pinfo, bfd_byte *end, size_t amt)
{
  attr->u.blk = read_blk(abfd, pinfo, end, amt);
  return attr->u.blk != NULL;
}

static inline void set_strx_attr(struct attribute *attr, struct comp_unit *unit)
{
  attr->u.str = unit->dwarf_str_offset != 0 ? (char *) read_indexed_string(attr->u.val, unit) : NULL;
}

static bfd_byte *
read_attribute_value (struct attribute *  attr,
		      unsigned		  form,
		      bfd_vma		  implicit_const,
		      struct comp_unit *  unit,
		      bfd_byte *	  info_ptr,
		      bfd_byte *	  info_ptr_end)
{
  bfd *abfd;
  size_t amt;

  if (attr == NULL || unit == NULL)
    {
      _bfd_error_handler (_("DWARF error: invalid NULL parameter"));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  abfd = unit->abfd;

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
	  attr->u.val = read_offset_sized_value(unit, &info_ptr, info_ptr_end);
	  break;
	}
    case DW_FORM_addr:
      attr->u.val = read_address (unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_GNU_ref_alt:
    case DW_FORM_sec_offset:
      attr->u.val = read_offset_sized_value(unit, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_block2:
      amt = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      if (!set_block_attr_from_size(attr, abfd, &info_ptr, info_ptr_end, amt))
	return NULL;
      break;

    case DW_FORM_block4:
      amt = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      if (!set_block_attr_from_size(attr, abfd, &info_ptr, info_ptr_end, amt))
	return NULL;
      break;

    case DW_FORM_ref1:
    case DW_FORM_flag:
    case DW_FORM_data1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx1:
      attr->u.val = read_1_byte (abfd, &info_ptr, info_ptr_end);
      attr->u.val = maybe_read_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_data2:
    case DW_FORM_ref2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      attr->u.val = maybe_read_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_addrx3:
      attr->u.val = read_3_bytes (abfd, &info_ptr, info_ptr_end);
      attr->u.val = maybe_read_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_ref4:
    case DW_FORM_data4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      break;

    case DW_FORM_addrx4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      attr->u.val = maybe_read_indexed_address(attr->u.val, unit);
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
      set_strx_attr(attr, unit);
      break;

    case DW_FORM_strx2:
      attr->u.val = read_2_bytes (abfd, &info_ptr, info_ptr_end);
      set_strx_attr(attr, unit);
      break;

    case DW_FORM_strx3:
      attr->u.val = read_3_bytes (abfd, &info_ptr, info_ptr_end);
      set_strx_attr(attr, unit);
      break;

    case DW_FORM_strx4:
      attr->u.val = read_4_bytes (abfd, &info_ptr, info_ptr_end);
      set_strx_attr(attr, unit);
      break;

    case DW_FORM_strx:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      set_strx_attr(attr, unit);
      break;

    case DW_FORM_exprloc:
    case DW_FORM_block:
      amt = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      if (!set_block_attr_from_size(attr, abfd, &info_ptr, info_ptr_end, amt))
	return NULL;
      break;

    case DW_FORM_block1:
      amt = read_1_byte (abfd, &info_ptr, info_ptr_end);
      if (!set_block_attr_from_size(attr, abfd, &info_ptr, info_ptr_end, amt))
	return NULL;
      break;

    case DW_FORM_sdata:
      attr->u.sval = _bfd_safe_read_leb128 (abfd, &info_ptr, true, info_ptr_end);
      break;

    case DW_FORM_rnglistx:
    case DW_FORM_loclistx:
    case DW_FORM_ref_udata:
    case DW_FORM_udata:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      break;

    case DW_FORM_addrx:
      attr->u.val = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      attr->u.val = maybe_read_indexed_address(attr->u.val, unit);
      break;

    case DW_FORM_indirect:
      form = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
      if (form == DW_FORM_implicit_const)
	implicit_const = _bfd_safe_read_leb128 (abfd, &info_ptr, true, info_ptr_end);
      info_ptr = read_attribute_value (attr, form, implicit_const, unit, info_ptr, info_ptr_end);
      if (info_ptr == NULL)
	return NULL;
      break;

    case DW_FORM_implicit_const:
      attr->form = DW_FORM_sdata;
      attr->u.sval = implicit_const;
      break;

    case DW_FORM_data16:
      if (!set_block_attr_from_size(attr, abfd, &info_ptr, info_ptr_end, 16))
	return NULL;
      break;

    default:
      _bfd_error_handler (_("DWARF error: invalid or unhandled FORM value: %#x"), form);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  return info_ptr;
}

/* Read an attribute described by an abbreviated attribute.  */

static bfd_byte *
read_attribute(struct attribute *attr,
               struct attr_abbrev *abbrev,
               struct comp_unit *unit,
               bfd_byte *info_ptr,
               bfd_byte *info_ptr_end)
{
  if (attr == NULL || abbrev == NULL || unit == NULL || info_ptr == NULL)
    return NULL;

  if (info_ptr_end != NULL && info_ptr > info_ptr_end)
    return NULL;

  attr->name = abbrev->name;

  return read_attribute_value(attr, abbrev->form, abbrev->implicit_const,
                              unit, info_ptr, info_ptr_end);
}

/* Return mangling style given LANG.  */

static int mangle_style(int lang)
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
  if (new_line == NULL || line == NULL)
    return false;

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
  struct line_sequence *seq_new = NULL;
  struct line_sequence *seq;
  struct line_info *last;
  struct line_info *info;
  size_t fname_len = 0;
  size_t alloc_size;

  if (table == NULL || table->abfd == NULL)
    return false;

  seq = table->sequences;
  last = seq ? seq->last_line : NULL;

  if (filename && filename[0])
    fname_len = strlen (filename) + 1;

  {
    bool is_duplicate = last
      && last->address == address
      && last->op_index == op_index
      && last->end_sequence == end_sequence;

    bool need_new_seq = (!is_duplicate) && (!seq || last->end_sequence);

    if (need_new_seq)
      {
        seq_new = (struct line_sequence *) bfd_malloc (sizeof (struct line_sequence));
        if (seq_new == NULL)
          return false;
      }

    alloc_size = sizeof (struct line_info) + fname_len;
    info = (struct line_info *) bfd_alloc (table->abfd, alloc_size);
    if (info == NULL)
      {
        if (seq_new)
          free (seq_new);
        return false;
      }

    info->prev_line = NULL;
    info->address = address;
    info->op_index = op_index;
    info->line = line;
    info->column = column;
    info->discriminator = discriminator;
    info->end_sequence = end_sequence;

    if (fname_len)
      {
        info->filename = (char *) (info + 1);
        memcpy (info->filename, filename, fname_len);
      }
    else
      {
        info->filename = NULL;
      }

    if (is_duplicate)
      {
        if (table->lcl_head == last)
          table->lcl_head = info;
        info->prev_line = last->prev_line;
        seq->last_line = info;
      }
    else if (need_new_seq)
      {
        seq = seq_new;
        seq->low_pc = address;
        seq->prev_sequence = table->sequences;
        seq->last_line = info;
        table->lcl_head = info;
        table->sequences = seq;
        table->num_sequences++;
      }
    else if (info->end_sequence
             || new_line_sorts_after (info, last))
      {
        info->prev_line = last;
        seq->last_line = info;
        if (!table->lcl_head)
          table->lcl_head = info;
      }
    else if (table->lcl_head
             && !new_line_sorts_after (info, table->lcl_head)
             && (!table->lcl_head->prev_line
                 || new_line_sorts_after (info, table->lcl_head->prev_line)))
      {
        info->prev_line = table->lcl_head->prev_line;
        table->lcl_head->prev_line = info;
      }
    else
      {
        struct line_info *li2 = seq->last_line; /* Always non-NULL.  */
        struct line_info *li1 = li2->prev_line;

        while (li1)
          {
            if (!new_line_sorts_after (info, li2)
                && new_line_sorts_after (info, li1))
              break;

            li2 = li1;
            li1 = li1->prev_line;
          }

        table->lcl_head = li2;
        info->prev_line = table->lcl_head->prev_line;
        table->lcl_head->prev_line = info;
        if (address < seq->low_pc)
          seq->low_pc = address;
      }
  }

  return true;
}

/* Extract a fully qualified filename from a line info table.
   The returned string has been malloc'ed and it is the caller's
   responsibility to free it.  */

static char *
concat_filename (struct line_info_table *table, unsigned int file)
{
  const char *filename;
  const char *dir_name = NULL;
  const char *subdir_name = NULL;

  if (table == NULL)
    {
      _bfd_error_handler (_("DWARF error: mangled line number section (bad file number)"));
      return strdup ("<unknown>");
    }

    if (!table->use_dir_and_file_0)
    {
      if (file == 0)
        return strdup ("<unknown>");
      --file;
    }

  if (file >= table->num_files)
    {
      _bfd_error_handler (_("DWARF error: mangled line number section (bad file number)"));
      return strdup ("<unknown>");
    }

  filename = table->files[file].name;
  if (filename == NULL)
    return strdup ("<unknown>");

  if (IS_ABSOLUTE_PATH (filename))
    return strdup (filename);

  {
    unsigned int dir = table->files[file].dir;
    if (!table->use_dir_and_file_0)
      --dir;

    if (dir < table->num_dirs)
      subdir_name = table->dirs[dir];

    if (!subdir_name || !IS_ABSOLUTE_PATH (subdir_name))
      dir_name = table->comp_dir;

    if (!dir_name)
      {
        dir_name = subdir_name;
        subdir_name = NULL;
      }
  }

  if (!dir_name)
    return strdup (filename);

  {
    size_t len_dir = strlen (dir_name);
    size_t len_file = strlen (filename);
    size_t len_sub = subdir_name ? strlen (subdir_name) : 0;
    size_t len = len_dir + len_file + 2 + (subdir_name ? len_sub + 1 : 0);
    char *name = (char *) bfd_malloc (len);
    if (!name)
      return NULL;

    if (subdir_name)
      snprintf (name, len, "%s/%s/%s", dir_name, subdir_name, filename);
    else
      snprintf (name, len, "%s/%s", dir_name, filename);

    return name;
  }
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

  bfd_vma early_low, early_high, late_low;

  if (low1 <= low2)
    {
      early_low = low1;
      early_high = high1;
      late_low = low2;
    }
  else
    {
      early_low = low2;
      early_high = high2;
      late_low = low1;
    }

  return late_low <= early_high;
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
  bfd_vma clamped_low_pc, clamped_high_pc;
  int ch, from_ch, to_ch;
  bool is_full_leaf = false;
  bool splitting_leaf_will_help = false;
  const unsigned int bucket_bits = 8;

  if (trie->num_room_in_leaf > 0)
    {
      struct trie_leaf *leaf = (struct trie_leaf *) trie;
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
	      return trie;
	    }
	}

      is_full_leaf = (leaf->num_stored_in_leaf == trie->num_room_in_leaf);

      if (is_full_leaf && trie_pc_bits < VMA_BITS)
	{
	  bfd_vma bucket_high_pc = trie_pc + (((bfd_vma) -1) >> trie_pc_bits);
	  for (i = 0; i < leaf->num_stored_in_leaf; ++i)
	    {
	      if (leaf->ranges[i].low_pc > trie_pc
		  || leaf->ranges[i].high_pc <= bucket_high_pc)
		{
		  splitting_leaf_will_help = true;
		  break;
		}
	    }
	}
    }

  if (is_full_leaf && splitting_leaf_will_help)
    {
      const struct trie_leaf *leaf = (struct trie_leaf *) trie;
      unsigned int i;

      trie = bfd_zalloc (abfd, sizeof (struct trie_interior));
      if (!trie)
	return NULL;
      is_full_leaf = false;

      for (i = 0; i < leaf->num_stored_in_leaf; ++i)
        {
	  if (!insert_arange_in_trie (abfd, trie, trie_pc, trie_pc_bits,
				      leaf->ranges[i].unit,
				      leaf->ranges[i].low_pc,
				      leaf->ranges[i].high_pc))
	    return NULL;
	}
    }

  if (is_full_leaf)
    {
      const struct trie_leaf *leaf = (const struct trie_leaf *) trie;
      unsigned int new_room_in_leaf = trie->num_room_in_leaf * 2;
      struct trie_leaf *new_leaf;
      size_t elem_size = sizeof (leaf->ranges[0]);
      size_t header_size = sizeof (*leaf);
      size_t amt;

#if defined(SIZE_MAX)
      if (new_room_in_leaf > SIZE_MAX / elem_size)
	return NULL;
      if (header_size > SIZE_MAX - (size_t)new_room_in_leaf * elem_size)
	return NULL;
#endif
      amt = header_size + (size_t)new_room_in_leaf * elem_size;

      new_leaf = bfd_zalloc (abfd, amt);
      if (!new_leaf)
	return NULL;

      new_leaf->head.num_room_in_leaf = new_room_in_leaf;
      new_leaf->num_stored_in_leaf = leaf->num_stored_in_leaf;

      if (leaf->num_stored_in_leaf > 0)
	memcpy (new_leaf->ranges,
		leaf->ranges,
		(size_t) leaf->num_stored_in_leaf * elem_size);

      trie = &new_leaf->head;
      is_full_leaf = false;
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

  clamped_low_pc = low_pc;
  clamped_high_pc = high_pc;
  if (trie_pc_bits > 0)
    {
      bfd_vma bucket_high_pc = trie_pc + (((bfd_vma) -1) >> trie_pc_bits);
      if (clamped_low_pc < trie_pc)
	clamped_low_pc = trie_pc;
      if (clamped_high_pc > bucket_high_pc)
	clamped_high_pc = bucket_high_pc;
    }

  from_ch = (int)((clamped_low_pc >> (VMA_BITS - trie_pc_bits - bucket_bits)) & 0xff);
  to_ch = (int)(((clamped_high_pc - 1) >> (VMA_BITS - trie_pc_bits - bucket_bits)) & 0xff);

  {
    struct trie_interior *interior = (struct trie_interior *) trie;
    for (ch = from_ch; ch <= to_ch; ++ch)
      {
	struct trie_node *child = interior->children[(unsigned char) ch];

	if (child == NULL)
	  {
	    child = alloc_trie_leaf (abfd);
	    if (!child)
	      return NULL;
	  }

	{
	  bfd_vma bucket = (bfd_vma) ((unsigned int) ch) << (VMA_BITS - trie_pc_bits - bucket_bits);
	  child = insert_arange_in_trie (abfd,
					 child,
					 trie_pc + bucket,
					 trie_pc_bits + bucket_bits,
					 unit,
					 low_pc,
					 high_pc);
	  if (!child)
	    return NULL;
	}

	interior->children[(unsigned char) ch] = child;
      }
  }

  return trie;
}

static bool
arange_add(struct comp_unit *unit, struct arange *first_arange,
           struct trie_node **trie_root, bfd_vma low_pc, bfd_vma high_pc)
{
  struct arange *arange;

  if (low_pc == high_pc)
    return true;

  if (unit == NULL || first_arange == NULL)
    return false;

  if (trie_root != NULL)
    {
      if (unit->file == NULL)
        return false;

      *trie_root = insert_arange_in_trie(unit->file->bfd_ptr,
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

  for (arange = first_arange; arange != NULL; arange = arange->next)
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
    }

  if (unit->abfd == NULL)
    return false;

  arange = bfd_alloc(unit->abfd, sizeof(*arange));
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
compare_sequences(const void *a, const void *b)
{
    if (a == b)
        return 0;
    if (a == NULL)
        return -1;
    if (b == NULL)
        return 1;

    const struct line_sequence *seq1 = (const struct line_sequence *)a;
    const struct line_sequence *seq2 = (const struct line_sequence *)b;

    if (seq1->low_pc != seq2->low_pc)
        return (seq1->low_pc < seq2->low_pc) ? -1 : 1;

    if (seq1->last_line != seq2->last_line) {
        if (seq1->last_line == NULL)
            return -1;
        if (seq2->last_line == NULL)
            return 1;

        if (seq1->last_line->address != seq2->last_line->address)
            return (seq1->last_line->address > seq2->last_line->address) ? -1 : 1;

        if (seq1->last_line->op_index != seq2->last_line->op_index)
            return (seq1->last_line->op_index > seq2->last_line->op_index) ? -1 : 1;
    }

    if (seq1->num_lines != seq2->num_lines)
        return (seq1->num_lines < seq2->num_lines) ? -1 : 1;

    return 0;
}

/* Construct the line information table for quick lookup.  */

static bool
build_line_info_table (struct line_info_table *  table,
		       struct line_sequence *    seq)
{
  size_t count;
  struct line_info **line_info_lookup;
  struct line_info *each_line;
  size_t line_index;
  size_t amt;

  if (table == NULL || seq == NULL || table->abfd == NULL)
    return false;

  if (seq->line_info_lookup != NULL)
    return true;

  count = 0;
  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    count++;

  if (count > (size_t) (unsigned int) -1)
    return false;

  seq->num_lines = (unsigned int) count;
  if (count == 0)
    return true;

  if (count > (size_t) -1 / sizeof (*line_info_lookup))
    return false;

  amt = count * sizeof (*line_info_lookup);
  line_info_lookup = (struct line_info **) bfd_alloc (table->abfd, amt);
  if (line_info_lookup == NULL)
    return false;

  line_index = count;
  for (each_line = seq->last_line; each_line; each_line = each_line->prev_line)
    line_info_lookup[--line_index] = each_line;

  BFD_ASSERT (line_index == 0);

  seq->line_info_lookup = line_info_lookup;

  return true;
}

/* Sort the line sequences for quick lookup.  */

static bool
sort_line_sequences (struct line_info_table* table)
{
  size_t amt;
  struct line_sequence *sequences;
  struct line_sequence *seq;
  unsigned int i = 0;
  unsigned int orig_num;
  unsigned int write_idx;
  bfd_vma last_high_pc;

  if (table == NULL)
    return false;

  orig_num = table->num_sequences;
  if (orig_num == 0)
    return true;

  if (orig_num > ((size_t) -1) / sizeof (struct line_sequence))
    return false;

  amt = sizeof (struct line_sequence) * (size_t) orig_num;
  sequences = (struct line_sequence *) bfd_alloc (table->abfd, amt);
  if (sequences == NULL)
    return false;

  seq = table->sequences;
  for (i = 0; i < orig_num; i++)
    {
      struct line_sequence* last_seq = seq;

      BFD_ASSERT (seq);
      sequences[i].low_pc = seq->low_pc;
      sequences[i].prev_sequence = NULL;
      sequences[i].last_line = seq->last_line;
      sequences[i].line_info_lookup = NULL;
      sequences[i].num_lines = i;
      seq = seq->prev_sequence;
      free (last_seq);
    }
  BFD_ASSERT (seq == NULL);

  qsort (sequences, orig_num, sizeof (struct line_sequence), compare_sequences);

  BFD_ASSERT (sequences[0].last_line);
  last_high_pc = sequences[0].last_line->address;
  write_idx = 1;

  for (i = 1; i < table->num_sequences; i++)
    {
      BFD_ASSERT (sequences[i].last_line);

      if (sequences[i].low_pc < last_high_pc)
        {
          if (sequences[i].last_line->address <= last_high_pc)
            continue;

          sequences[i].low_pc = last_high_pc;
        }

      last_high_pc = sequences[i].last_line->address;

      if (i != write_idx)
        {
          sequences[write_idx].low_pc = sequences[i].low_pc;
          sequences[write_idx].last_line = sequences[i].last_line;
        }
      write_idx++;
    }

  table->sequences = sequences;
  table->num_sequences = write_idx;
  return true;
}

/* Add directory to TABLE.  CUR_DIR memory ownership is taken by TABLE.  */

static bool
line_info_add_include_dir(struct line_info_table *table, char *cur_dir)
{
  if (table == NULL)
    return false;

  size_t chunk = (size_t) DIR_ALLOC_CHUNK;
  if (chunk == 0)
    return false;

  if ((table->dirs == NULL) || ((table->num_dirs % chunk) == 0))
    {
      size_t max = (size_t) -1;
      if (table->num_dirs > max - chunk)
        return false;

      size_t new_count = table->num_dirs + chunk;
      if (new_count > max / sizeof(*table->dirs))
        return false;

      size_t bytes = new_count * sizeof(*table->dirs);
      char **tmp = bfd_realloc(table->dirs, bytes);
      if (tmp == NULL)
        return false;

      table->dirs = tmp;
    }

  table->dirs[table->num_dirs++] = cur_dir;
  return true;
}

static bool
line_info_add_include_dir_stub(struct line_info_table *table, char *cur_dir,
                               unsigned int dir ATTRIBUTE_UNUSED,
                               unsigned int xtime ATTRIBUTE_UNUSED,
                               unsigned int size ATTRIBUTE_UNUSED)
{
    (void)dir;
    (void)xtime;
    (void)size;
    return line_info_add_include_dir(table, cur_dir);
}

/* Add file to TABLE.  CUR_FILE memory ownership is taken by TABLE.  */

static bool
line_info_add_file_name(struct line_info_table *table, char *cur_file,
                        unsigned int dir, unsigned int xtime,
                        unsigned int size)
{
  if (table == NULL)
    return false;

  size_t count = (size_t) table->num_files;

  if ((count % FILE_ALLOC_CHUNK) == 0)
    {
      size_t new_count = count + (size_t) FILE_ALLOC_CHUNK;
      if (new_count < count)
        return false;

      size_t bytes = new_count * sizeof(struct fileinfo);
      if (bytes / sizeof(struct fileinfo) != new_count)
        return false;

      struct fileinfo *tmp = bfd_realloc(table->files, bytes);
      if (tmp == NULL)
        return false;

      table->files = tmp;
    }

  struct fileinfo *fi = &table->files[table->num_files];
  fi->name = cur_file;
  fi->dir = dir;
  fi->time = xtime;
  fi->size = size;

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
  bfd_byte *format_header;

  format_count = read_1_byte (abfd, &buf, buf_end);
  format_header = buf;

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
      bfd_byte *format_cursor = format_header;
      struct fileinfo fe;
      memset (&fe, 0, sizeof fe);

      for (formati = 0; formati < format_count; formati++)
	{
	  bfd_vma content_type;
	  bfd_vma form;
	  struct attribute attr;

	  content_type = _bfd_safe_read_leb128 (abfd, &format_cursor, false, buf_end);
	  switch (content_type)
	    {
	    case DW_LNCT_path:
	    case DW_LNCT_directory_index:
	    case DW_LNCT_timestamp:
	    case DW_LNCT_size:
	    case DW_LNCT_MD5:
	      break;
	    default:
	      _bfd_error_handler
		(_("DWARF error: unknown format content type %" PRIu64),
		 (uint64_t) content_type);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }

	  form = _bfd_safe_read_leb128 (abfd, &format_cursor, false, buf_end);
	  buf = read_attribute_value (&attr, form, 0, unit, buf, buf_end);
	  if (buf == NULL)
	    return false;

	  switch (content_type)
	    {
	    case DW_LNCT_path:
	      switch (form)
		{
		case DW_FORM_string:
		case DW_FORM_line_strp:
		case DW_FORM_strx:
		case DW_FORM_strx1:
		case DW_FORM_strx2:
		case DW_FORM_strx3:
		case DW_FORM_strx4:
		  fe.name = attr.u.str;
		  break;
		default:
		  break;
		}
	      break;

	    case DW_LNCT_directory_index:
	      switch (form)
		{
		case DW_FORM_data1:
		case DW_FORM_data2:
		case DW_FORM_data4:
		case DW_FORM_data8:
		case DW_FORM_udata:
		  fe.dir = attr.u.val;
		  break;
		default:
		  break;
		}
	      break;

	    case DW_LNCT_timestamp:
	      switch (form)
		{
		case DW_FORM_data1:
		case DW_FORM_data2:
		case DW_FORM_data4:
		case DW_FORM_data8:
		case DW_FORM_udata:
		  fe.time = attr.u.val;
		  break;
		default:
		  break;
		}
	      break;

	    case DW_LNCT_size:
	      switch (form)
		{
		case DW_FORM_data1:
		case DW_FORM_data2:
		case DW_FORM_data4:
		case DW_FORM_data8:
		case DW_FORM_udata:
		  fe.size = attr.u.val;
		  break;
		default:
		  break;
		}
	      break;

	    case DW_LNCT_MD5:
	      /* Ignore regardless of form; DW_FORM_data16 carries the MD5.  */
	      break;
	    }
	}

      if (!callback (table, fe.name, fe.dir, fe.time, fe.size))
	return false;
    }

  *bufp = buf;
  return true;
}

/* Decode the line number information for UNIT.  */

static struct line_info_table*
decode_line_info (struct comp_unit *unit)
{
  bfd *abfd;
  struct dwarf2_debug *stash;
  struct dwarf2_debug_file *file;
  struct line_info_table* table;
  bfd_byte *line_ptr;
  bfd_byte *line_end;
  struct line_head lh;
  unsigned int i, offset_size;
  char *cur_file, *cur_dir;
  unsigned char op_code, extended_op, adj_opcode;
  unsigned int exop_len;
  size_t amt;

  if (unit == NULL || unit->file == NULL || unit->stash == NULL || unit->abfd == NULL)
    return NULL;

  abfd = unit->abfd;
  stash = unit->stash;
  file = unit->file;

  if (unit->line_offset == 0 && file->line_table)
    return file->line_table;

  if (! read_section (abfd, &stash->debug_sections[debug_line],
                      file->syms, unit->line_offset,
                      &file->dwarf_line_buffer, &file->dwarf_line_size))
    return NULL;

  if (file->dwarf_line_size < 16 || unit->line_offset >= file->dwarf_line_size)
    {
      _bfd_error_handler
        (_("DWARF error: line info section is too small (%" PRId64 ")"),
         (int64_t) file->dwarf_line_size);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  line_ptr = file->dwarf_line_buffer + unit->line_offset;
  line_end = file->dwarf_line_buffer + file->dwarf_line_size;

  lh.total_length = read_4_bytes (abfd, &line_ptr, line_end);
  offset_size = 4;
  if (lh.total_length == 0xffffffff)
    {
      lh.total_length = read_8_bytes (abfd, &line_ptr, line_end);
      offset_size = 8;
    }
  else if (lh.total_length == 0 && unit->addr_size == 8)
    {
      lh.total_length = read_4_bytes (abfd, &line_ptr, line_end);
      offset_size = 8;
    }

  if (lh.total_length > (size_t) (line_end - line_ptr))
    {
      _bfd_error_handler
        (_("DWARF error: line info data is bigger (%#" PRIx64 ") than the space remaining in the section (%#lx)"),
         (uint64_t) lh.total_length, (unsigned long) (line_end - line_ptr));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  line_end = line_ptr + lh.total_length;

  lh.version = read_2_bytes (abfd, &line_ptr, line_end);
  if (lh.version < 2 || lh.version > 5)
    {
      _bfd_error_handler
        (_("DWARF error: unhandled .debug_line version %d"), lh.version);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  if (line_ptr + offset_size + (lh.version >= 5 ? 8 : (lh.version >= 4 ? 6 : 5)) >= line_end)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading prologue"));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  if (lh.version >= 5)
    {
      unsigned int segment_selector_size;
      read_1_byte (abfd, &line_ptr, line_end);
      segment_selector_size = read_1_byte (abfd, &line_ptr, line_end);
      if (segment_selector_size != 0)
        {
          _bfd_error_handler
            (_("DWARF error: line info unsupported segment selector size %u"),
             segment_selector_size);
          bfd_set_error (bfd_error_bad_value);
          return NULL;
        }
    }

  if (offset_size == 4)
    lh.prologue_length = read_4_bytes (abfd, &line_ptr, line_end);
  else
    lh.prologue_length = read_8_bytes (abfd, &line_ptr, line_end);

  lh.minimum_instruction_length = read_1_byte (abfd, &line_ptr, line_end);

  if (lh.version >= 4)
    lh.maximum_ops_per_insn = read_1_byte (abfd, &line_ptr, line_end);
  else
    lh.maximum_ops_per_insn = 1;

  if (lh.maximum_ops_per_insn == 0)
    {
      _bfd_error_handler
        (_("DWARF error: invalid maximum operations per instruction"));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  lh.default_is_stmt = read_1_byte (abfd, &line_ptr, line_end);
  lh.line_base = read_1_signed_byte (abfd, &line_ptr, line_end);
  lh.line_range = read_1_byte (abfd, &line_ptr, line_end);
  lh.opcode_base = read_1_byte (abfd, &line_ptr, line_end);

  if (lh.opcode_base == 0 || line_ptr + (lh.opcode_base - 1) >= line_end)
    {
      _bfd_error_handler (_("DWARF error: ran out of room reading opcodes"));
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  amt = lh.opcode_base * sizeof (unsigned char);
  lh.standard_opcode_lengths = (unsigned char *) bfd_alloc (abfd, amt);
  if (lh.standard_opcode_lengths == NULL)
    return NULL;

  lh.standard_opcode_lengths[0] = 1;

  for (i = 1; i < lh.opcode_base; ++i)
    lh.standard_opcode_lengths[i] = read_1_byte (abfd, &line_ptr, line_end);

  amt = sizeof (struct line_info_table);
  table = (struct line_info_table *) bfd_alloc (abfd, amt);
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

  if (lh.version >= 5)
    {
      if (!read_formatted_entries (unit, &line_ptr, line_end, table,
                                   line_info_add_include_dir_stub))
        goto fail;
      if (!read_formatted_entries (unit, &line_ptr, line_end, table,
                                   line_info_add_file_name))
        goto fail;
      table->use_dir_and_file_0 = true;
    }
  else
    {
      while ((cur_dir = read_string (&line_ptr, line_end)) != NULL)
        {
          if (!line_info_add_include_dir (table, cur_dir))
            goto fail;
        }
      while ((cur_file = read_string (&line_ptr, line_end)) != NULL)
        {
          unsigned int dir, xtime, size;
          dir = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
          xtime = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
          size = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
          if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
            goto fail;
        }
      table->use_dir_and_file_0 = false;
    }

  while (line_ptr < line_end)
    {
      bfd_vma address = 0;
      unsigned char op_index = 0;
      char * filename = NULL;
      unsigned int line = 1;
      unsigned int column = 0;
      unsigned int discriminator = 0;
      int is_stmt = lh.default_is_stmt;
      int end_sequence = 0;
      unsigned int dir, xtime, size;
      bfd_vma low_pc  = (bfd_vma) -1;
      bfd_vma high_pc = 0;

      if (table->num_files)
        filename = concat_filename (table, 1);

      while (!end_sequence && line_ptr < line_end)
        {
          op_code = read_1_byte (abfd, &line_ptr, line_end);

          if (op_code >= lh.opcode_base)
            {
              adj_opcode = op_code - lh.opcode_base;
              if (lh.line_range == 0)
                goto line_fail;
              if (lh.maximum_ops_per_insn == 1)
                address += (adj_opcode / lh.line_range
                            * lh.minimum_instruction_length);
              else
                {
                  address += ((op_index + adj_opcode / lh.line_range)
                              / lh.maximum_ops_per_insn
                              * lh.minimum_instruction_length);
                  op_index = ((op_index + adj_opcode / lh.line_range)
                              % lh.maximum_ops_per_insn);
                }
              line += lh.line_base + (adj_opcode % lh.line_range);
              if (!add_line_info (table, address, op_index, filename,
                                  line, column, discriminator, 0))
                goto line_fail;
              discriminator = 0;
              if (address < low_pc)
                low_pc = address;
              if (address > high_pc)
                high_pc = address;
            }
          else switch (op_code)
            {
            case DW_LNS_extended_op:
              exop_len = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
              extended_op = read_1_byte (abfd, &line_ptr, line_end);

              switch (extended_op)
                {
                case DW_LNE_end_sequence:
                  end_sequence = 1;
                  if (!add_line_info (table, address, op_index, filename, line,
                                      column, discriminator, end_sequence))
                    goto line_fail;
                  discriminator = 0;
                  if (address < low_pc)
                    low_pc = address;
                  if (address > high_pc)
                    high_pc = address;
                  if (!arange_add (unit, &unit->arange, &unit->file->trie_root,
                                   low_pc, high_pc))
                    goto line_fail;
                  break;
                case DW_LNE_set_address:
                  address = read_address (unit, &line_ptr, line_end);
                  op_index = 0;
                  break;
                case DW_LNE_define_file:
                  cur_file = read_string (&line_ptr, line_end);
                  dir = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                  xtime = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                  size = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                  if (!line_info_add_file_name (table, cur_file, dir, xtime, size))
                    goto line_fail;
                  break;
                case DW_LNE_set_discriminator:
                  discriminator = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                  break;
                case DW_LNE_HP_source_file_correlation:
                  if (exop_len == 0 || line_ptr + (exop_len - 1) > line_end)
                    goto line_fail;
                  line_ptr += exop_len - 1;
                  break;
                default:
                  _bfd_error_handler (_("DWARF error: mangled line number section"));
                  bfd_set_error (bfd_error_bad_value);
                line_fail:
                  free (filename);
                  goto fail;
                }
              break;
            case DW_LNS_copy:
              if (!add_line_info (table, address, op_index,
                                  filename, line, column, discriminator, 0))
                goto line_fail;
              discriminator = 0;
              if (address < low_pc)
                low_pc = address;
              if (address > high_pc)
                high_pc = address;
              break;
            case DW_LNS_advance_pc:
              if (lh.maximum_ops_per_insn == 1)
                address += (lh.minimum_instruction_length
                            * _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end));
              else
                {
                  bfd_vma adjust = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                  address = ((op_index + adjust) / lh.maximum_ops_per_insn
                             * lh.minimum_instruction_length);
                  op_index = (op_index + adjust) % lh.maximum_ops_per_insn;
                }
              break;
            case DW_LNS_advance_line:
              line += _bfd_safe_read_leb128 (abfd, &line_ptr, true, line_end);
              break;
            case DW_LNS_set_file:
              {
                unsigned int filenum;
                filenum = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
                free (filename);
                filename = concat_filename (table, filenum);
                break;
              }
            case DW_LNS_set_column:
              column = _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
              break;
            case DW_LNS_negate_stmt:
              is_stmt = (!is_stmt);
              break;
            case DW_LNS_set_basic_block:
              break;
            case DW_LNS_const_add_pc:
              if (lh.line_range == 0)
                goto line_fail;
              if (lh.maximum_ops_per_insn == 1)
                address += (lh.minimum_instruction_length
                            * ((255 - lh.opcode_base) / lh.line_range));
              else
                {
                  bfd_vma adjust = ((255 - lh.opcode_base) / lh.line_range);
                  address += (lh.minimum_instruction_length
                              * ((op_index + adjust) / lh.maximum_ops_per_insn));
                  op_index = (op_index + adjust) % lh.maximum_ops_per_insn;
                }
              break;
            case DW_LNS_fixed_advance_pc:
              address += read_2_bytes (abfd, &line_ptr, line_end);
              op_index = 0;
              break;
            default:
              {
                unsigned int cnt = lh.standard_opcode_lengths[op_code];
                for (i = 0; i < cnt; i++)
                  (void) _bfd_safe_read_leb128 (abfd, &line_ptr, false, line_end);
              }
              break;
            }
        }

      free (filename);
    }

  if (unit->line_offset == 0)
    file->line_table = table;
  if (!sort_line_sequences (table))
    goto fail;
  return table;

fail:
  while (table && table->sequences != NULL)
    {
      struct line_sequence* seq = table->sequences;
      table->sequences = table->sequences->prev_sequence;
      free (seq);
    }
  if (table)
    {
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
lookup_address_in_line_info_table(struct line_info_table *table,
                                  bfd_vma addr,
                                  const char **filename_ptr,
                                  unsigned int *linenumber_ptr,
                                  unsigned int *discriminator_ptr)
{
  struct line_sequence *seq = NULL;
  struct line_info *info = NULL;
  int low, high, mid;

  if (!filename_ptr || !table)
    return false;

  *filename_ptr = NULL;

  if (!table->sequences || table->num_sequences == 0)
    return false;

  low = 0;
  high = (int) table->num_sequences;
  while (low < high)
    {
      mid = low + (high - low) / 2;
      seq = &table->sequences[mid];
      if (!seq || !seq->last_line)
        break;

      if (addr < seq->low_pc)
        high = mid;
      else if (addr >= seq->last_line->address)
        low = mid + 1;
      else
        break;
    }

  if (!seq || !seq->last_line || addr < seq->low_pc || addr >= seq->last_line->address)
    return false;

  if (!build_line_info_table(table, seq))
    return false;

  if (!seq->line_info_lookup || seq->num_lines < 2)
    return false;

  low = 0;
  high = (int) seq->num_lines - 2;
  while (low <= high)
    {
      struct line_info *curr;
      struct line_info *next;

      mid = low + (high - low) / 2;
      curr = seq->line_info_lookup[mid];
      next = seq->line_info_lookup[mid + 1];

      if (!curr || !next)
        break;

      if (addr < curr->address)
        high = mid - 1;
      else if (addr >= next->address)
        low = mid + 1;
      else
        {
          info = curr;
          break;
        }
    }

  if (info && addr >= info->address
      && !(info->end_sequence || info == seq->last_line))
    {
      *filename_ptr = info->filename;
      *linenumber_ptr = info->line;
      if (discriminator_ptr)
        *discriminator_ptr = info->discriminator;
      return true;
    }

  return false;
}

/* Read in the .debug_ranges section for future reference.  */

static bool
read_debug_ranges(struct comp_unit *unit)
{
    if (unit == NULL || unit->stash == NULL || unit->file == NULL) {
        return false;
    }

    struct dwarf2_debug *stash = unit->stash;
    struct dwarf2_debug_file *file = unit->file;

    return read_section(unit->abfd, &stash->debug_sections[debug_ranges],
                        file->syms, 0,
                        &file->dwarf_ranges_buffer, &file->dwarf_ranges_size);
}

/* Read in the .debug_rnglists section for future reference.  */

static bool
read_debug_rnglists(struct comp_unit *unit)
{
  if (unit == NULL)
    return false;

  if (unit->stash == NULL || unit->file == NULL || unit->abfd == NULL)
    return false;

  struct dwarf2_debug *stash = unit->stash;
  struct dwarf2_debug_file *file = unit->file;

  return read_section(unit->abfd,
                      &stash->debug_sections[debug_rnglists],
                      file->syms,
                      0,
                      &file->dwarf_rnglists_buffer,
                      &file->dwarf_rnglists_size);
}

/* Function table functions.  */

static int
compare_lookup_funcinfos(const void *a, const void *b)
{
  if (a == b)
    return 0;
  if (a == NULL)
    return -1;
  if (b == NULL)
    return 1;

  const struct lookup_funcinfo *lookup1 = (const struct lookup_funcinfo *)a;
  const struct lookup_funcinfo *lookup2 = (const struct lookup_funcinfo *)b;

  int cmp = (lookup1->low_addr > lookup2->low_addr) - (lookup1->low_addr < lookup2->low_addr);
  if (cmp != 0)
    return cmp;

  cmp = (lookup1->high_addr > lookup2->high_addr) - (lookup1->high_addr < lookup2->high_addr);
  if (cmp != 0)
    return cmp;

  return (lookup1->idx > lookup2->idx) - (lookup1->idx < lookup2->idx);
}

static bool
build_lookup_funcinfo_table(struct comp_unit *unit)
{
  if (unit == NULL)
    return false;

  if (unit->lookup_funcinfo_table != NULL || unit->number_of_functions == 0)
    return true;

  size_t n = unit->number_of_functions;
  if (n > ((size_t)-1) / sizeof(struct lookup_funcinfo))
    return false;

  struct lookup_funcinfo *table = (struct lookup_funcinfo *) bfd_malloc(n * sizeof(struct lookup_funcinfo));
  if (table == NULL)
    return false;

  size_t remaining = n;
  struct funcinfo *fi = unit->function_table;
  while (fi != NULL && remaining > 0)
    {
      size_t pos = --remaining;
      struct lookup_funcinfo *e = &table[pos];
      e->funcinfo = fi;
      e->idx = pos;

      bfd_vma low = fi->arange.low;
      bfd_vma high = fi->arange.high;

      for (struct arange *r = fi->arange.next; r != NULL; r = r->next)
        {
          if (r->low < low)
            low = r->low;
          if (r->high > high)
            high = r->high;
        }

      e->low_addr = low;
      e->high_addr = high;

      fi = fi->prev_func;
    }

  if (fi != NULL || remaining != 0)
    {
      free(table);
      return false;
    }

  qsort(table, n, sizeof(struct lookup_funcinfo), compare_lookup_funcinfos);

  bfd_vma max_high = table[0].high_addr;
  for (size_t i = 1; i < n; i++)
    {
      if (table[i].high_addr > max_high)
        max_high = table[i].high_addr;
      else
        table[i].high_addr = max_high;
    }

  unit->lookup_funcinfo_table = table;
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
  unsigned int number_of_functions;
  const struct lookup_funcinfo *table;
  bfd_size_type low, high, mid, first;
  struct funcinfo *best_fit;
  bfd_vma best_fit_len;
  bfd_size_type i;
  struct funcinfo *fi;
  struct arange *arange;
  bfd_vma lowa, higha, len;

  if (unit == NULL || function_ptr == NULL)
    return false;

  number_of_functions = unit->number_of_functions;
  if (number_of_functions == 0)
    return false;

  if (!build_lookup_funcinfo_table (unit))
    return false;

  table = unit->lookup_funcinfo_table;

  if (table[number_of_functions - 1].high_addr < addr)
    return false;

  low = 0;
  high = number_of_functions;
  first = high;

  while (low < high)
    {
      mid = low + (high - low) / 2;
      if (addr < table[mid].low_addr)
        high = mid;
      else if (addr >= table[mid].high_addr)
        low = mid + 1;
      else
        {
          first = mid;
          high = mid;
        }
    }

  best_fit = NULL;
  best_fit_len = (bfd_vma) -1;

  for (i = first; i < number_of_functions; ++i)
    {
      if (addr < table[i].low_addr)
        break;

      fi = table[i].funcinfo;

      for (arange = &fi->arange; arange; arange = arange->next)
        {
          lowa = arange->low;
          higha = arange->high;

          if (addr < lowa || addr >= higha)
            continue;

          len = higha - lowa;

          if (len < best_fit_len
              || (len == best_fit_len && fi > best_fit))
            {
              best_fit = fi;
              best_fit_len = len;
            }
        }
    }

  if (!best_fit)
    return false;

  *function_ptr = best_fit;
  return true;
}

/* If SYM at ADDR is within function table of UNIT, set FILENAME_PTR
   and LINENUMBER_PTR, and return TRUE.  */

static bool
lookup_symbol_in_function_table(struct comp_unit *unit,
                                asymbol *sym,
                                bfd_vma addr,
                                const char **filename_ptr,
                                unsigned int *linenumber_ptr)
{
  if (!unit || !sym || !filename_ptr || !linenumber_ptr)
    return false;

  const char *symbol_name = bfd_asymbol_name(sym);
  if (!symbol_name)
    return false;

  struct funcinfo *best_fit = NULL;
  bfd_vma best_fit_len = (bfd_vma)-1;

  for (struct funcinfo *fi = unit->function_table; fi; fi = fi->prev_func)
    {
      if (!fi->file || !fi->name)
        continue;

      for (struct arange *ar = &fi->arange; ar; ar = ar->next)
        {
          if (!(addr >= ar->low && addr < ar->high))
            continue;

          if (strstr(symbol_name, fi->name) == NULL)
            continue;

          bfd_vma range_len = ar->high - ar->low;
          if (range_len < best_fit_len)
            {
              best_fit = fi;
              best_fit_len = range_len;
            }
        }
    }

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
lookup_symbol_in_variable_table(struct comp_unit *unit,
                                asymbol *sym,
                                bfd_vma addr,
                                const char **filename_ptr,
                                unsigned int *linenumber_ptr)
{
  if (unit == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

  const char *name = bfd_asymbol_name(sym);
  if (name == NULL)
    return false;

  for (struct varinfo *var = unit->variable_table; var != NULL; var = var->prev_var)
    {
      if (var->addr != addr)
        continue;
      if (var->stack)
        continue;
      if (var->file == NULL || var->name == NULL)
        continue;
      if (strstr(name, var->name) == NULL)
        continue;

      *filename_ptr = var->file;
      *linenumber_ptr = var->line;
      return true;
    }

  return false;
}

static struct comp_unit *stash_comp_unit (struct dwarf2_debug *,
					  struct dwarf2_debug_file *);
static bool comp_unit_maybe_decode_line_info (struct comp_unit *);

static bool locate_comp_unit_for_ptr(struct comp_unit **unitp,
                                     bfd_byte *info_ptr,
                                     bfd_byte **info_ptr_end,
                                     bool is_alt)
{
  if (info_ptr >= (*unitp)->info_ptr_unit && info_ptr < (*unitp)->end_ptr)
    {
      *info_ptr_end = (*unitp)->end_ptr;
      return true;
    }

  {
    struct comp_unit *u = NULL;
    struct addr_range range = { info_ptr, info_ptr };
    splay_tree_node v = splay_tree_lookup ((*unitp)->file->comp_unit_tree,
                                           (splay_tree_key) &range);
    if (v != NULL)
      u = (struct comp_unit *) v->value;

    if (u == NULL)
      {
        for (;;)
          {
            struct comp_unit *t = stash_comp_unit ((*unitp)->stash,
                                                   is_alt ? &(*unitp)->stash->alt
                                                          : &(*unitp)->stash->f);
            if (t == NULL)
              break;
            if (info_ptr >= t->info_ptr_unit && info_ptr < t->end_ptr)
              {
                u = t;
                break;
              }
          }
      }

    if (u == NULL)
      return false;

    *unitp = u;
    *info_ptr_end = u->end_ptr;
    return true;
  }
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
  bfd *abfd = unit->abfd;
  bfd_byte *info_ptr = NULL;
  bfd_byte *info_ptr_end = NULL;
  unsigned int abbrev_number, i;
  struct abbrev_info *abbrev;
  uint64_t die_ref = attr_ptr->u.val;
  struct attribute attr;

  if (recur_count == 100)
    {
      _bfd_error_handler (_("DWARF error: abstract instance recursion detected"));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (attr_ptr->form == DW_FORM_ref_addr)
    {
      size_t total;
      info_ptr = unit->file->dwarf_info_buffer;
      info_ptr_end = info_ptr + unit->file->dwarf_info_size;
      total = (size_t) (info_ptr_end - info_ptr);
      if (!die_ref)
        return true;
      if (die_ref >= total)
        {
          _bfd_error_handler (_("DWARF error: invalid abstract instance DIE ref"));
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
      info_ptr += die_ref;

      if (!locate_comp_unit_for_ptr (&unit, info_ptr, &info_ptr_end, false))
        {
          _bfd_error_handler (_("DWARF error: unable to locate abstract instance DIE ref %" PRIu64),
                              (uint64_t) die_ref);
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
    }
  else if (attr_ptr->form == DW_FORM_GNU_ref_alt)
    {
      bool first_time = unit->stash->alt.dwarf_info_buffer == NULL;
      info_ptr = read_alt_indirect_ref (unit, die_ref);
      if (first_time)
        unit->stash->alt.info_ptr = unit->stash->alt.dwarf_info_buffer;
      if (info_ptr == NULL)
        {
          _bfd_error_handler (_("DWARF error: unable to read alt ref %" PRIu64),
                              (uint64_t) die_ref);
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
      info_ptr_end = (unit->stash->alt.dwarf_info_buffer
                      + unit->stash->alt.dwarf_info_size);
      if (unit->stash->alt.all_comp_units)
        unit = unit->stash->alt.all_comp_units;

      if (!locate_comp_unit_for_ptr (&unit, info_ptr, &info_ptr_end, true))
        {
          _bfd_error_handler (_("DWARF error: unable to locate abstract instance DIE ref %" PRIu64),
                              (uint64_t) die_ref);
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
    }
  else
    {
      size_t total;
      info_ptr = unit->info_ptr_unit;
      info_ptr_end = unit->end_ptr;
      total = (size_t) (info_ptr_end - info_ptr);
      if (!die_ref || die_ref >= total)
        {
          _bfd_error_handler (_("DWARF error: invalid abstract instance DIE ref"));
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
      info_ptr += die_ref;
    }

  abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, info_ptr_end);
  if (abbrev_number == 0)
    return true;

  abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
  if (!abbrev)
    {
      _bfd_error_handler (_("DWARF error: could not find abbrev number %u"), abbrev_number);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  for (i = 0; i < abbrev->num_attrs; ++i)
    {
      info_ptr = read_attribute (&attr, &abbrev->attrs[i], unit, info_ptr, info_ptr_end);
      if (info_ptr == NULL)
        break;

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
              && !find_abstract_instance (unit, &attr, recur_count + 1,
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

static bool
read_ranges(struct comp_unit *unit, struct arange *arange, struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *ranges_ptr;
  bfd_byte *ranges_end;
  bfd_vma base_address;
  size_t addr_bytes;
  size_t two_addr_bytes;

  if (!unit || !arange || !trie_root || !unit->file)
    return false;

  if (!unit->file->dwarf_ranges_buffer && !read_debug_ranges(unit))
    return false;

  if (offset > unit->file->dwarf_ranges_size)
    return false;

  ranges_ptr = unit->file->dwarf_ranges_buffer + (size_t) offset;
  ranges_end = unit->file->dwarf_ranges_buffer + unit->file->dwarf_ranges_size;
  base_address = unit->base_address;

  addr_bytes = (size_t) unit->addr_size;
  two_addr_bytes = addr_bytes << 1;
  if (two_addr_bytes < addr_bytes)
    return false;

  for (;;) {
    size_t remaining = (size_t) (ranges_end - ranges_ptr);
    bfd_vma low_pc;
    bfd_vma high_pc;

    if (remaining < two_addr_bytes)
      return false;

    low_pc = read_address(unit, &ranges_ptr, ranges_end);
    high_pc = read_address(unit, &ranges_ptr, ranges_end);

    if (low_pc == 0 && high_pc == 0)
      break;

    if (low_pc == (bfd_vma) -1 && high_pc != (bfd_vma) -1) {
      base_address = high_pc;
    } else {
      if (!arange_add(unit, arange, trie_root, base_address + low_pc, base_address + high_pc))
        return false;
    }
  }

  return true;
}

static inline size_t bytes_left(const bfd_byte *p, const bfd_byte *end)
{
  return (size_t)(end - p);
}

static inline bool have_bytes(const bfd_byte *p, const bfd_byte *end, size_t n)
{
  return p <= end && bytes_left(p, end) >= n;
}

static inline bool vma_add_safe(bfd_vma a, bfd_vma b, bfd_vma *out)
{
  bfd_vma r = a + b;
  if (r < a)
    return false;
  *out = r;
  return true;
}

static bool
read_rnglists (struct comp_unit *unit, struct arange *arange,
	       struct trie_node **trie_root, uint64_t offset)
{
  bfd_byte *rngs_ptr;
  bfd_byte *rngs_end;
  bfd_vma base_address;
  bfd_vma low_pc = 0;
  bfd_vma high_pc = 0;
  bfd *abfd;

  if (!unit || !arange || !trie_root || !unit->file)
    return false;

  abfd = unit->abfd;
  if (!abfd)
    return false;

  if (!unit->file->dwarf_rnglists_buffer)
    {
      if (!read_debug_rnglists (unit))
	return false;
      if (!unit->file->dwarf_rnglists_buffer)
	return false;
    }

  {
    uint64_t buf_size64 = (uint64_t) unit->file->dwarf_rnglists_size;
    if (offset > buf_size64)
      return false;
  }

  rngs_ptr = unit->file->dwarf_rnglists_buffer + (size_t) offset;
  rngs_end = unit->file->dwarf_rnglists_buffer + (size_t) unit->file->dwarf_rnglists_size;

  base_address = unit->base_address;

  for (;;)
    {
      enum dwarf_range_list_entry rlet;

      if (rngs_ptr >= rngs_end)
	return false;

      rlet = read_1_byte (abfd, &rngs_ptr, rngs_end);

      switch (rlet)
	{
	case DW_RLE_end_of_list:
	  return true;

	case DW_RLE_base_address:
	  if (!have_bytes (rngs_ptr, rngs_end, unit->addr_size))
	    return false;
	  base_address = read_address (unit, &rngs_ptr, rngs_end);
	  continue;

	case DW_RLE_start_length:
	  {
	    bfd_vma length;
	    if (!have_bytes (rngs_ptr, rngs_end, unit->addr_size))
	      return false;
	    low_pc = read_address (unit, &rngs_ptr, rngs_end);
	    length = _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	    if (!vma_add_safe (low_pc, length, &high_pc))
	      return false;
	    break;
	  }

	case DW_RLE_offset_pair:
	  {
	    bfd_vma dlow = _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	    bfd_vma dhigh = _bfd_safe_read_leb128 (abfd, &rngs_ptr, false, rngs_end);
	    if (!vma_add_safe (base_address, dlow, &low_pc))
	      return false;
	    if (!vma_add_safe (base_address, dhigh, &high_pc))
	      return false;
	    break;
	  }

	case DW_RLE_start_end:
	  {
	    size_t avail = bytes_left (rngs_ptr, rngs_end);
	    size_t need = unit->addr_size;
	    if (need > avail || avail - need < need)
	      return false;
	    low_pc = read_address (unit, &rngs_ptr, rngs_end);
	    high_pc = read_address (unit, &rngs_ptr, rngs_end);
	    break;
	  }

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

static bool
read_rangelist (struct comp_unit *unit, struct arange *arange,
		struct trie_node **trie_root, uint64_t offset)
{
  if (unit == NULL || arange == NULL || trie_root == NULL)
    return false;

  return (unit->version <= 4)
    ? read_ranges (unit, arange, trie_root, offset)
    : read_rnglists (unit, arange, trie_root, offset);
}

static struct funcinfo *
lookup_func_by_offset (uint64_t offset, struct funcinfo *table)
{
  struct funcinfo *current = table;

  while (current != NULL)
    {
      if (current->unit_offset == offset)
        return current;
      current = current->prev_func;
    }

  return NULL;
}

static struct varinfo *
lookup_var_by_offset(uint64_t offset, struct varinfo *table)
{
    for (struct varinfo *node = table; node != NULL; node = node->prev_var)
    {
        if (node->unit_offset == offset)
            return node;
    }
    return NULL;
}


/* DWARF2 Compilation unit functions.  */

static struct funcinfo *
reverse_funcinfo_list(struct funcinfo *head)
{
  struct funcinfo *new_head = NULL;
  struct funcinfo *current = head;
  struct funcinfo *next = NULL;

  while (current != NULL)
    {
      next = current->prev_func;
      current->prev_func = new_head;
      new_head = current;
      current = next;
    }

  return new_head;
}

static struct varinfo *
reverse_varinfo_list(struct varinfo *head)
{
    struct varinfo *new_head = NULL;
    struct varinfo *next;

    while (head != NULL)
    {
        next = head->prev_var;
        head->prev_var = new_head;
        new_head = head;
        head = next;
    }
    return new_head;
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
  } *nested_funcs = NULL;
  size_t nested_funcs_size = 32;
  bool success = false;

  nested_funcs = (struct nest_funcinfo *)
    bfd_malloc (nested_funcs_size * sizeof (*nested_funcs));
  if (nested_funcs == NULL)
    goto cleanup;
  nested_funcs[nesting_level].func = NULL;

  while (nesting_level >= 0)
    {
      unsigned int abbrev_number, i;
      struct abbrev_info *abbrev;
      struct funcinfo *func;
      uint64_t current_offset;

      if (info_ptr >= info_ptr_end)
        goto cleanup;

      current_offset = (uint64_t) (info_ptr - unit->info_ptr_unit);
      abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr,
                                             false, info_ptr_end);
      if (abbrev_number == 0)
        {
          nesting_level--;
          continue;
        }

      abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
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
          goto cleanup;
        }

      if (abbrev->tag == DW_TAG_subprogram
          || abbrev->tag == DW_TAG_entry_point
          || abbrev->tag == DW_TAG_inlined_subroutine)
        {
          size_t amt = sizeof (struct funcinfo);
          func = (struct funcinfo *) bfd_zalloc (abfd, amt);
          if (func == NULL)
            goto cleanup;

          func->tag = abbrev->tag;
          func->prev_func = unit->function_table;
          func->unit_offset = current_offset;
          unit->function_table = func;
          unit->number_of_functions++;
          BFD_ASSERT (!unit->cached);

          if (func->tag == DW_TAG_inlined_subroutine)
            {
              unsigned int j = nesting_level;
              while (j-- != 0)
                {
                  if (nested_funcs[j].func)
                    {
                      func->caller_func = nested_funcs[j].func;
                      break;
                    }
                }
            }
          nested_funcs[nesting_level].func = func;
        }
      else
        {
          if (abbrev->tag == DW_TAG_variable
              || abbrev->tag == DW_TAG_member)
            {
              size_t amt = sizeof (struct varinfo);
              struct varinfo *v = (struct varinfo *) bfd_zalloc (abfd, amt);
              if (v == NULL)
                goto cleanup;
              v->tag = abbrev->tag;
              v->stack = true;
              v->prev_var = unit->variable_table;
              unit->variable_table = v;
              v->unit_offset = current_offset;
            }
          nested_funcs[nesting_level].func = NULL;
        }

      for (i = 0; i < abbrev->num_attrs; ++i)
        {
          struct attribute attr;
          info_ptr = read_attribute (&attr, &abbrev->attrs[i],
                                     unit, info_ptr, info_ptr_end);
          if (info_ptr == NULL)
            goto cleanup;
        }

      if (abbrev->has_children)
        {
          nesting_level++;
          if ((size_t) nesting_level >= nested_funcs_size)
            {
              size_t new_size;
              struct nest_funcinfo *tmp;
              if (nested_funcs_size > SIZE_MAX / 2)
                goto cleanup;
              new_size = nested_funcs_size * 2;
              if (new_size > SIZE_MAX / sizeof (*nested_funcs))
                goto cleanup;
              tmp = (struct nest_funcinfo *)
                bfd_realloc (nested_funcs, new_size * sizeof (*nested_funcs));
              if (tmp == NULL)
                goto cleanup;
              nested_funcs = tmp;
              nested_funcs_size = new_size;
            }
          nested_funcs[nesting_level].func = NULL;
        }
    }

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  info_ptr = unit->first_child_die_ptr;
  nesting_level = 0;

  {
    struct funcinfo *last_func = NULL;
    struct varinfo *last_var = NULL;

    while (nesting_level >= 0)
      {
        unsigned int abbrev_number, i;
        struct abbrev_info *abbrev;
        struct attribute attr;
        struct funcinfo *func = NULL;
        struct varinfo *var = NULL;
        bfd_vma low_pc = 0;
        bfd_vma high_pc = 0;
        bool high_pc_relative = false;
        uint64_t current_offset;

        if (info_ptr >= info_ptr_end)
          goto cleanup;

        current_offset = (uint64_t) (info_ptr - unit->info_ptr_unit);
        abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr,
                                               false, info_ptr_end);
        if (abbrev_number == 0)
          {
            nesting_level--;
            continue;
          }

        abbrev = lookup_abbrev (abbrev_number, unit->abbrevs);
        BFD_ASSERT (abbrev != NULL);

        if (abbrev->tag == DW_TAG_subprogram
            || abbrev->tag == DW_TAG_entry_point
            || abbrev->tag == DW_TAG_inlined_subroutine)
          {
            if (last_func
                && last_func->prev_func
                && last_func->prev_func->unit_offset == current_offset)
              func = last_func->prev_func;
            else
              func = lookup_func_by_offset (current_offset, unit->function_table);

            if (func == NULL)
              goto cleanup;
            last_func = func;
          }
        else if (abbrev->tag == DW_TAG_variable
                 || abbrev->tag == DW_TAG_member)
          {
            if (last_var
                && last_var->prev_var
                && last_var->prev_var->unit_offset == current_offset)
              var = last_var->prev_var;
            else
              var = lookup_var_by_offset (current_offset, unit->variable_table);

            if (var == NULL)
              goto cleanup;
            last_var = var;
          }

        for (i = 0; i < abbrev->num_attrs; ++i)
          {
            info_ptr = read_attribute (&attr, &abbrev->attrs[i],
                                       unit, info_ptr, info_ptr_end);
            if (info_ptr == NULL)
              goto cleanup;

            if (func)
              {
                switch (attr.name)
                  {
                  case DW_AT_call_file:
                    if (is_int_form (&attr))
                      {
                        free (func->caller_file);
                        func->caller_file = concat_filename (unit->line_table,
                                                             attr.u.val);
                      }
                    break;

                  case DW_AT_call_line:
                    if (is_int_form (&attr))
                      func->caller_line = attr.u.val;
                    break;

                  case DW_AT_abstract_origin:
                  case DW_AT_specification:
                    if (is_int_form (&attr)
                        && !find_abstract_instance (unit, &attr, 0,
                                                    &func->name,
                                                    &func->is_linkage,
                                                    &func->file,
                                                    &func->line))
                      goto cleanup;
                    break;

                  case DW_AT_name:
                    if (func->name == NULL && is_str_form (&attr))
                      {
                        func->name = attr.u.str;
                        if (mangle_style (unit->lang) == 0)
                          func->is_linkage = true;
                      }
                    break;

                  case DW_AT_linkage_name:
                  case DW_AT_MIPS_linkage_name:
                    if (is_str_form (&attr))
                      {
                        func->name = attr.u.str;
                        func->is_linkage = true;
                      }
                    break;

                  case DW_AT_low_pc:
                    if (is_int_form (&attr))
                      low_pc = attr.u.val;
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
                        && !read_rangelist (unit, &func->arange,
                                            &unit->file->trie_root, attr.u.val))
                      goto cleanup;
                    break;

                  case DW_AT_decl_file:
                    if (is_int_form (&attr))
                      {
                        free (func->file);
                        func->file = concat_filename (unit->line_table,
                                                      attr.u.val);
                      }
                    break;

                  case DW_AT_decl_line:
                    if (is_int_form (&attr))
                      func->line = attr.u.val;
                    break;

                  default:
                    break;
                  }
              }
            else if (var)
              {
                switch (attr.name)
                  {
                  case DW_AT_specification:
                    if (is_int_form (&attr) && attr.u.val)
                      {
                        bool is_linkage;
                        if (!find_abstract_instance (unit, &attr, 0,
                                                     &var->name,
                                                     &is_linkage,
                                                     &var->file,
                                                     &var->line))
                          {
                            _bfd_error_handler (_("DWARF error: could not find "
                                                  "variable specification "
                                                  "at offset 0x%lx"),
                                                (unsigned long) attr.u.val);
                            break;
                          }
                      }
                    break;

                  case DW_AT_name:
                    if (is_str_form (&attr))
                      var->name = attr.u.str;
                    break;

                  case DW_AT_decl_file:
                    if (is_int_form (&attr))
                      {
                        free (var->file);
                        var->file = concat_filename (unit->line_table,
                                                     attr.u.val);
                      }
                    break;

                  case DW_AT_decl_line:
                    if (is_int_form (&attr))
                      var->line = attr.u.val;
                    break;

                  case DW_AT_external:
                    if (is_int_form (&attr) && attr.u.val != 0)
                      var->stack = false;
                    break;

                  case DW_AT_location:
                    switch (attr.form)
                      {
                      case DW_FORM_block:
                      case DW_FORM_block1:
                      case DW_FORM_block2:
                      case DW_FORM_block4:
                      case DW_FORM_exprloc:
                        if (attr.u.blk->data != NULL
                            && *attr.u.blk->data == DW_OP_addr)
                          {
                            var->stack = false;
                            if (attr.u.blk->size == unit->addr_size + 1U)
                              var->addr = bfd_get (unit->addr_size * 8,
                                                   unit->abfd,
                                                   attr.u.blk->data + 1);
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
          }

        if (abbrev->has_children)
          nesting_level++;

        if (high_pc_relative)
          high_pc += low_pc;

        if (func && high_pc != 0)
          {
            if (!arange_add (unit, &func->arange, &unit->file->trie_root,
                             low_pc, high_pc))
              goto cleanup;
          }
      }
  }

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  success = true;

cleanup:
  free (nested_funcs);
  return success;
}

/* Read the attributes of the form strx and addrx.  */

static void
reread_attribute(struct comp_unit *unit,
                 struct attribute *attr,
                 bfd_vma *low_pc,
                 bfd_vma *high_pc,
                 bool *high_pc_relative,
                 bool compunit)
{
    if (!unit || !attr || !low_pc || !high_pc || !high_pc_relative)
        return;

    if (is_strx_form(attr->form))
        attr->u.str = (char *) read_indexed_string(attr->u.val, unit);
    if (is_addrx_form(attr->form))
        attr->u.val = read_indexed_address(attr->u.val, unit);

    switch (attr->name)
    {
        case DW_AT_stmt_list:
            unit->stmtlist = 1;
            unit->line_offset = attr->u.val;
            break;

        case DW_AT_name:
            if (is_str_form(attr))
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
            if (!unit->file)
                return;
            if (!read_rangelist(unit, &unit->arange, &unit->file->trie_root, attr->u.val))
                return;
            break;

        case DW_AT_comp_dir:
        {
            char *comp_dir = attr->u.str;

            if (!is_str_form(attr))
            {
                _bfd_error_handler(_("DWARF error: DW_AT_comp_dir attribute encountered with a non-string form"));
                comp_dir = NULL;
            }

            if (comp_dir)
            {
                char *cp = strchr(comp_dir, ':');
                if (cp && cp != comp_dir && cp[-1] == '.' && cp[1] == '/')
                    comp_dir = cp + 1;
            }
            unit->comp_dir = comp_dir;
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
      if ((size_t)(end_ptr - info_ptr) < 8 + offset_size)
	{
	  _bfd_error_handler (_("DWARF error: insufficient data in unit header"));
	  bfd_set_error (bfd_error_bad_value);
	  return NULL;
	}
      info_ptr += 8;
      info_ptr += offset_size;
      break;

    case DW_UT_skeleton:
      if ((size_t)(end_ptr - info_ptr) < 8)
	{
	  _bfd_error_handler (_("DWARF error: insufficient data in unit header"));
	  bfd_set_error (bfd_error_bad_value);
	  return NULL;
	}
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

  abbrev_number = _bfd_safe_read_leb128 (abfd, &info_ptr, false, end_ptr);
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

  compunit_flag = (abbrev->tag == DW_TAG_compile_unit);

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
	      size_t new_alloc = str_alloc ? (str_alloc * 2 + 200) : 200;
	      if (new_alloc < str_count + 1)
		new_alloc = str_count + 1;
	      if (new_alloc > ((size_t)-1) / sizeof (*str_addrp))
		goto err_exit;
	      {
		void *tmp = bfd_realloc (str_addrp, new_alloc * sizeof (*str_addrp));
		if (tmp == NULL)
		  goto err_exit;
		str_addrp = (struct attribute *) tmp;
		str_alloc = new_alloc;
	      }
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
      if (!arange_add (unit, &unit->arange, &unit->file->trie_root, low_pc, high_pc))
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
comp_unit_may_contain_address(struct comp_unit *unit, bfd_vma addr)
{
    if (unit == NULL)
        return false;

    if (unit->error)
        return false;

    if (unit->arange.high == 0 || unit->line_table == NULL)
        return true;

    const struct arange *current = &unit->arange;
    while (current != NULL) {
        bfd_vma low = current->low;
        bfd_vma high = current->high;

        if (low < high && addr >= low && addr < high)
            return true;

        current = current->next;
    }

    return false;
}

/* If UNIT contains ADDR, set the output parameters to the values for
   the line containing ADDR and return TRUE.  Otherwise return FALSE.
   The output parameters, FILENAME_PTR, FUNCTION_PTR, and
   LINENUMBER_PTR, are pointers to the objects to be filled in.  */

static bool
comp_unit_find_nearest_line(struct comp_unit *unit,
                            bfd_vma addr,
                            const char **filename_ptr,
                            struct funcinfo **function_ptr,
                            unsigned int *linenumber_ptr,
                            unsigned int *discriminator_ptr)
{
  if (unit == NULL)
    return false;

  if (!comp_unit_maybe_decode_line_info(unit))
    return false;

  if (function_ptr != NULL)
    *function_ptr = NULL;

  struct funcinfo *found_func = NULL;
  bool func_p = lookup_address_in_function_table(unit, addr, &found_func);

  if (func_p && found_func != NULL && found_func->tag == DW_TAG_inlined_subroutine && unit->stash != NULL)
    unit->stash->inliner_chain = found_func;

  const char *found_filename = NULL;
  unsigned int found_line = 0;
  unsigned int found_discriminator = 0;

  bool line_p = lookup_address_in_line_info_table(unit->line_table, addr,
                                                  &found_filename,
                                                  &found_line,
                                                  &found_discriminator);

  if (function_ptr != NULL)
    *function_ptr = found_func;

  if (line_p)
    {
      if (filename_ptr != NULL)
        *filename_ptr = found_filename;
      if (linenumber_ptr != NULL)
        *linenumber_ptr = found_line;
      if (discriminator_ptr != NULL)
        *discriminator_ptr = found_discriminator;
    }

  return line_p || func_p;
}

/* Check to see if line info is already decoded in a comp_unit.
   If not, decode it.  Returns TRUE if no errors were encountered;
   FALSE otherwise.  */

static bool
comp_unit_maybe_decode_line_info(struct comp_unit *unit)
{
    if (unit == NULL || unit->error)
        return false;

    if (unit->line_table)
        return true;

    if (unit->stmtlist == NULL) {
        unit->error = 1;
        return false;
    }

    unit->line_table = decode_line_info(unit);
    if (unit->line_table == NULL) {
        unit->error = 1;
        return false;
    }

    if (unit->first_child_die_ptr < unit->end_ptr &&
        !scan_unit_for_symbols(unit)) {
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
comp_unit_find_line(struct comp_unit *unit,
                    asymbol *sym,
                    bfd_vma addr,
                    const char **filename_ptr,
                    unsigned int *linenumber_ptr)
{
    if (unit == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
        return false;

    if (!comp_unit_maybe_decode_line_info(unit))
        return false;

    if ((sym->flags & BSF_FUNCTION) != 0)
        return lookup_symbol_in_function_table(unit, sym, addr, filename_ptr, linenumber_ptr);

    return lookup_symbol_in_variable_table(unit, sym, addr, filename_ptr, linenumber_ptr);
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
  struct funcinfo *func;
  struct varinfo *var;
  bool ok = true;

  BFD_ASSERT (stash->info_hash_status != STASH_INFO_HASH_DISABLED);

  if (!comp_unit_maybe_decode_line_info (unit))
    return false;

  BFD_ASSERT (!unit->cached);

  unit->function_table = reverse_funcinfo_list (unit->function_table);
  for (func = unit->function_table; func != NULL; func = func->prev_func)
    {
      if (!func->name)
        continue;

      ok = insert_info_hash_table (funcinfo_hash_table, func->name,
                                   (void *) func, false);
      if (!ok)
        break;
    }
  unit->function_table = reverse_funcinfo_list (unit->function_table);
  if (!ok)
    return false;

  unit->variable_table = reverse_varinfo_list (unit->variable_table);
  for (var = unit->variable_table; var != NULL; var = var->prev_var)
    {
      if (var->stack || var->file == NULL || var->name == NULL)
        continue;

      ok = insert_info_hash_table (varinfo_hash_table, var->name,
                                   (void *) var, false);
      if (!ok)
        break;
    }
  unit->variable_table = reverse_varinfo_list (unit->variable_table);

  unit->cached = true;
  return ok;
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
  const char *uncomp;
  const char *comp;

  if (abfd == NULL || debug_sections == NULL)
    return NULL;

  uncomp = debug_sections[debug_info].uncompressed_name;
  comp = debug_sections[debug_info].compressed_name;

  if (after_sec == NULL)
    {
      if (uncomp != NULL)
        {
          msec = bfd_get_section_by_name (abfd, uncomp);
          if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
            return msec;
        }

      if (comp != NULL)
        {
          msec = bfd_get_section_by_name (abfd, comp);
          if (msec != NULL && (msec->flags & SEC_HAS_CONTENTS) != 0)
            return msec;
        }

      for (msec = abfd->sections; msec != NULL; msec = msec->next)
        if ((msec->flags & SEC_HAS_CONTENTS) != 0
            && startswith (msec->name, GNU_LINKONCE_INFO))
          return msec;

      return NULL;
    }

  for (msec = after_sec->next; msec != NULL; msec = msec->next)
    {
      if ((msec->flags & SEC_HAS_CONTENTS) == 0)
        continue;

      if (uncomp != NULL && strcmp (msec->name, uncomp) == 0)
        return msec;

      if (comp != NULL && strcmp (msec->name, comp) == 0)
        return msec;

      if (startswith (msec->name, GNU_LINKONCE_INFO))
        return msec;
    }

  return NULL;
}

/* Transfer VMAs from object file to separate debug file.  */

static void set_debug_vma(bfd *orig_bfd, bfd *debug_bfd)
{
    if (orig_bfd == NULL || debug_bfd == NULL) {
        return;
    }

    asection *src = orig_bfd->sections;
    asection *dst = debug_bfd->sections;

    while (src != NULL && dst != NULL) {
        if ((dst->flags & SEC_DEBUGGING) != 0) {
            break;
        }

        const char *src_name = src->name;
        const char *dst_name = dst->name;

        if (src_name != NULL && dst_name != NULL && strcmp(src_name, dst_name) == 0) {
            dst->output_section = src->output_section;
            dst->output_offset = src->output_offset;
            dst->vma = src->vma;
        }

        src = src->next;
        dst = dst->next;
    }
}

/* If the dwarf2 info was found in a separate debug file, return the
   debug file section corresponding to the section in the original file
   and the debug file symbols.  */

static void
_bfd_dwarf2_stash_syms (struct dwarf2_debug *stash, bfd *abfd,
                        asection **sec, asymbol ***syms)
{
  asection *src, *dst;
  bfd *target_bfd;

  if (stash == NULL || abfd == NULL || sec == NULL || syms == NULL)
    return;

  target_bfd = stash->f.bfd_ptr;
  if (target_bfd == abfd)
    return;

  if (*sec == NULL)
    {
      *syms = stash->f.syms;
      return;
    }

  if (target_bfd == NULL)
    return;

  for (src = abfd->sections, dst = target_bfd->sections;
       src != NULL && dst != NULL;
       src = src->next, dst = dst->next)
    {
      if ((dst->flags & SEC_DEBUGGING) != 0)
        break;

      if (src == *sec)
        {
          const char *src_name = src->name;
          const char *dst_name = dst->name;

          if (src_name != NULL && dst_name != NULL && strcmp (src_name, dst_name) == 0)
            {
              *sec = dst;
              *syms = stash->f.syms;
            }
          break;
        }
    }
}

/* Unset vmas for adjusted sections in STASH.  */

static void
unset_sections(struct dwarf2_debug *stash)
{
    if (stash == NULL || stash->adjusted_sections == NULL || stash->adjusted_section_count <= 0) {
        return;
    }

    size_t count = (size_t)stash->adjusted_section_count;
    struct adjusted_section *sections = stash->adjusted_sections;

    for (size_t idx = 0; idx < count; ++idx) {
        struct adjusted_section *sec = &sections[idx];
        if (sec->section != NULL) {
            sec->section->vma = sec->orig_vma;
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

static inline bfd_vma
align_up (bfd_vma value, unsigned int alignment_power)
{
  if (alignment_power == 0)
    return value;
  bfd_vma mask = ((bfd_vma) 1 << alignment_power) - 1;
  return (value + mask) & ~mask;
}

static bool
section_is_candidate (asection *sect, bfd *current_bfd, bfd *orig_bfd, const char *debug_info_name)
{
  if (sect->output_section != NULL
      && sect->output_section != sect
      && (sect->flags & SEC_DEBUGGING) == 0)
    return false;

  {
    int is_debug_info = (strcmp (sect->name, debug_info_name) == 0
                         || startswith (sect->name, GNU_LINKONCE_INFO));
    if (!(((sect->flags & SEC_ALLOC) != 0) && current_bfd == orig_bfd) && !is_debug_info)
      return false;
  }

  return true;
}

static bool
place_sections (bfd *orig_bfd, struct dwarf2_debug *stash)
{
  if (stash->adjusted_section_count != 0)
    {
      int i = stash->adjusted_section_count;
      struct adjusted_section *p = stash->adjusted_sections;
      for (; i > 0; i--, p++)
        p->section->vma = p->adj_vma;
      return true;
    }

  {
    const char *debug_info_name = stash->debug_sections[debug_info].uncompressed_name;
    bfd *bfds[2] = { orig_bfd, stash->f.bfd_ptr };
    int nbfds = (stash->f.bfd_ptr != orig_bfd) ? 2 : 1;
    size_t count = 0;

    for (int bi = 0; bi < nbfds; ++bi)
      {
        bfd *abfd = bfds[bi];
        for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
          {
            if (section_is_candidate (sect, abfd, orig_bfd, debug_info_name))
              count++;
          }
      }

    if (count <= 1)
      {
        stash->adjusted_section_count = -1;
      }
    else
      {
        if ((size_t) (int) count != count)
          return false;

        size_t item_size = sizeof (struct adjusted_section);
        if (item_size != 0 && count > (size_t) -1 / item_size)
          return false;

        size_t amt = count * item_size;
        struct adjusted_section *p = (struct adjusted_section *) bfd_malloc (amt);
        if (p == NULL)
          return false;

        stash->adjusted_sections = p;
        stash->adjusted_section_count = (int) count;

        bfd_vma last_vma = 0, last_dwarf = 0;

        for (int bi = 0; bi < nbfds; ++bi)
          {
            bfd *abfd = bfds[bi];
            for (asection *sect = abfd->sections; sect != NULL; sect = sect->next)
              {
                if (!section_is_candidate (sect, abfd, orig_bfd, debug_info_name))
                  continue;

                bfd_size_type sz = sect->rawsize ? sect->rawsize : sect->size;
                int is_debug_info = (strcmp (sect->name, debug_info_name) == 0
                                     || startswith (sect->name, GNU_LINKONCE_INFO));

                p->section = sect;
                p->orig_vma = sect->vma;

                bfd_vma *v = is_debug_info ? &last_dwarf : &last_vma;
                bfd_vma new_vma = align_up (*v, sect->alignment_power);
                sect->vma = new_vma;
                *v = new_vma + sz;

                p->adj_vma = sect->vma;
                p++;
              }
          }
      }

    if (orig_bfd != stash->f.bfd_ptr)
      set_debug_vma (orig_bfd, stash->f.bfd_ptr);
  }

  return true;
}

/* Look up a funcinfo by name using the given info hash table.  If found,
   also update the locations pointed to by filename_ptr and linenumber_ptr.

   This function returns TRUE if a funcinfo that matches the given symbol
   and address is found with any error; otherwise it returns FALSE.  */

static bool
info_hash_lookup_funcinfo(struct info_hash_table *hash_table,
                          asymbol *sym,
                          bfd_vma addr,
                          const char **filename_ptr,
                          unsigned int *linenumber_ptr)
{
  if (hash_table == NULL || sym == NULL || filename_ptr == NULL || linenumber_ptr == NULL)
    return false;

  const char *name = bfd_asymbol_name(sym);
  if (name == NULL)
    return false;

  const struct funcinfo *best_func = NULL;
  bfd_vma best_len = (bfd_vma)-1;

  for (struct info_list_node *node = lookup_info_hash_table(hash_table, name);
       node != NULL;
       node = node->next)
    {
      const struct funcinfo *func = (const struct funcinfo *) node->info;
      if (func == NULL)
        continue;

      for (const struct arange *r = &func->arange; r != NULL; r = r->next)
        {
          if (addr >= r->low && addr < r->high)
            {
              bfd_vma len = r->high - r->low;
              if (len < best_len)
                {
                  best_len = len;
                  best_func = func;
                }
            }
        }
    }

  if (best_func == NULL)
    return false;

  *filename_ptr = best_func->file;
  *linenumber_ptr = best_func->line;
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
  const char *name;
  struct info_list_node *node;
  struct varinfo *var_info;

  if (!hash_table || !sym || !filename_ptr || !linenumber_ptr)
    return false;

  name = bfd_asymbol_name (sym);
  if (name == NULL)
    return false;

  node = lookup_info_hash_table (hash_table, name);
  while (node != NULL)
    {
      var_info = node->info;
      if (var_info != NULL && var_info->addr == addr)
        {
          *filename_ptr = var_info->file;
          *linenumber_ptr = var_info->line;
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
stash_maybe_update_info_hash_tables(struct dwarf2_debug *stash)
{
    if (stash == NULL)
        return false;

    struct comp_unit *head = stash->hash_units_head;

    if (stash->f.all_comp_units == head)
        return true;

    struct comp_unit *unit = head ? head->prev_unit : stash->f.last_comp_unit;

    for (; unit != NULL; unit = unit->prev_unit)
    {
        if (!comp_unit_hash_info(stash, unit,
                                 stash->funcinfo_hash_table,
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
  if (stash == NULL)
    return;

  BFD_ASSERT (stash->info_hash_status == STASH_INFO_HASH_OFF);

  if (stash->info_hash_count++ < STASH_INFO_HASH_TRIGGER)
    return;

  if (abfd == NULL)
    {
      stash->info_hash_status = STASH_INFO_HASH_DISABLED;
      return;
    }

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
  BFD_ASSERT (stash != NULL);
  BFD_ASSERT (sym != NULL);
  BFD_ASSERT (filename_ptr != NULL);
  BFD_ASSERT (linenumber_ptr != NULL);
  BFD_ASSERT (stash->info_hash_status == STASH_INFO_HASH_ON);

  const bool is_function = (sym->flags & BSF_FUNCTION) != 0;

  if (is_function)
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
  size_t i;
  size_t count;

  if (abfd == NULL || stash == NULL)
    return false;

  count = abfd->section_count;
  if (count == 0)
    return true;

  if (count > ((size_t) -1) / sizeof (*stash->sec_vma))
    return false;

  stash->sec_vma = bfd_malloc (sizeof (*stash->sec_vma) * count);
  if (stash->sec_vma == NULL)
    return false;

  stash->sec_vma_count = count;

  for (i = 0, s = abfd->sections; s != NULL && i < count; ++i, s = s->next)
    {
      asection *out = s->output_section;
      stash->sec_vma[i] = (out != NULL) ? (out->vma + s->output_offset) : s->vma;
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
section_vma_same(const bfd *abfd, const struct dwarf2_debug *stash)
{
    const asection *s;
    unsigned int i;

    if (abfd == NULL || stash == NULL || stash->sec_vma == NULL)
        return false;

    if (abfd->section_count != stash->sec_vma_count)
        return false;

    s = abfd->sections;
    for (i = 0; i < abfd->section_count; i++) {
        bfd_vma vma;
        if (s == NULL)
            return false;

        vma = (s->output_section != NULL)
              ? (s->output_section->vma + s->output_offset)
              : s->vma;

        if (vma != stash->sec_vma[i])
            return false;

        s = s->next;
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
  bfd_size_type total_size = 0;
  asection *msec = NULL;
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
      if (!stash)
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
  if (!stash->f.abbrev_offsets)
    return false;

  stash->alt.abbrev_offsets = htab_create_alloc (10, hash_abbrev, eq_abbrev,
						 del_abbrev, calloc, free);
  if (!stash->alt.abbrev_offsets)
    return false;

  stash->f.trie_root = alloc_trie_leaf (abfd);
  if (!stash->f.trie_root)
    return false;

  stash->alt.trie_root = alloc_trie_leaf (abfd);
  if (!stash->alt.trie_root)
    return false;

  if (debug_bfd == NULL)
    debug_bfd = abfd;

  msec = find_debug_info (debug_bfd, debug_sections, NULL);
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
      if (!bfd_check_format (debug_bfd, bfd_object)
	  || (msec = find_debug_info (debug_bfd, debug_sections, NULL)) == NULL
	  || !bfd_generic_link_read_symbols (debug_bfd))
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

  if (!find_debug_info (debug_bfd, debug_sections, msec))
    {
      total_size = bfd_get_section_limit_octets (debug_bfd, msec);
      if (!read_section (debug_bfd, &stash->debug_sections[debug_info],
			 symbols, 0,
			 &stash->f.dwarf_info_buffer, &total_size))
	goto restore_vma;
    }
  else
    {
      asection *sec;

      total_size = 0;
      for (sec = msec; sec; sec = find_debug_info (debug_bfd, debug_sections, sec))
	{
	  if (bfd_section_size_insane (debug_bfd, sec))
	    goto restore_vma;

	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, sec);
	  if (total_size + readsz < total_size)
	    {
	      bfd_set_error (bfd_error_no_memory);
	      goto restore_vma;
	    }
	  total_size += readsz;
	}

      stash->f.dwarf_info_buffer = (bfd_byte *) bfd_malloc (total_size);
      if (stash->f.dwarf_info_buffer == NULL)
	goto restore_vma;

      bfd_size_type offset = 0;
      for (sec = msec; sec; sec = find_debug_info (debug_bfd, debug_sections, sec))
	{
	  bfd_size_type readsz = bfd_get_section_limit_octets (debug_bfd, sec);
	  if (readsz == 0)
	    continue;

	  if (!bfd_simple_get_relocated_section_contents (debug_bfd, sec,
							   stash->f.dwarf_info_buffer + offset,
							   symbols))
	    goto restore_vma;

	  offset += readsz;
	}
      total_size = offset;
    }

  stash->f.info_ptr = stash->f.dwarf_info_buffer;
  stash->f.dwarf_info_size = total_size;
  return true;

restore_vma:
  unset_sections (stash);
  return false;
}

/* Parse the next DWARF2 compilation unit at FILE->INFO_PTR.  */

static struct comp_unit *
stash_comp_unit (struct dwarf2_debug *stash, struct dwarf2_debug_file *file)
{
  bfd_size_type length;
  unsigned int offset_size = 4;
  bfd_byte *info_ptr_end = file->dwarf_info_buffer + file->dwarf_info_size;
  bfd_byte *info_ptr_unit = file->info_ptr;

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

  if (length == 0 || length > (size_t) (info_ptr_end - file->info_ptr))
    {
      file->info_ptr = info_ptr_end;
      return NULL;
    }

  {
    struct comp_unit *each = parse_comp_unit (stash, file,
                                              file->info_ptr, length,
                                              info_ptr_unit, offset_size);
    if (!each)
      {
        file->info_ptr = info_ptr_end;
        return NULL;
      }

    if (file->comp_unit_tree == NULL)
      {
        file->comp_unit_tree
          = splay_tree_new (splay_tree_compare_addr_range,
                            splay_tree_free_addr_range, NULL);
        if (file->comp_unit_tree == NULL)
          {
            file->info_ptr = info_ptr_end;
            return NULL;
          }
      }

    {
      struct addr_range *r = (struct addr_range *) bfd_malloc (sizeof (*r));
      splay_tree_node v;

      if (r == NULL)
        {
          file->info_ptr = info_ptr_end;
          return NULL;
        }

      r->start = each->info_ptr_unit;
      r->end = each->end_ptr;

      v = splay_tree_lookup (file->comp_unit_tree, (splay_tree_key) r);
      if (v != NULL || r->end <= r->start)
        abort ();

      splay_tree_insert (file->comp_unit_tree, (splay_tree_key) r,
                         (splay_tree_value) each);
    }

    if (file->all_comp_units)
      file->all_comp_units->prev_unit = each;
    else
      file->last_comp_unit = each;

    each->next_unit = file->all_comp_units;
    file->all_comp_units = each;

    if (each->arange.high == 0)
      {
        each->next_unit_without_ranges = file->all_comp_units_without_ranges;
        file->all_comp_units_without_ranges = each;
      }

    file->info_ptr += length;
    return each;
  }
}

/* Hash function for an asymbol.  */

static hashval_t
hash_asymbol (const void *sym)
{
  const asymbol *asym = (const asymbol *) sym;
  const char *name;

  if (asym == NULL)
    return 0;

  name = asym->name;
  if (name == NULL)
    return 0;

  return htab_hash_string (name);
}

/* Equality function for asymbols.  */

static int
eq_asymbol(const void *a, const void *b)
{
  if (a == NULL || b == NULL)
    return 0;

  const asymbol *sa = (const asymbol *) a;
  const asymbol *sb = (const asymbol *) b;

  const char *name_a = sa->name;
  const char *name_b = sb->name;

  if (name_a == NULL || name_b == NULL)
    return 0;

  return strcmp(name_a, name_b) == 0;
}

/* Scan the debug information in PINFO looking for a DW_TAG_subprogram
   abbrev with a DW_AT_low_pc attached to it.  Then lookup that same
   symbol in SYMBOLS and return the difference between the low_pc and
   the symbol's address.  Returns 0 if no suitable symbol could be found.  */

bfd_signed_vma
_bfd_dwarf2_find_symbol_bias (asymbol **symbols, void **pinfo)
{
  struct dwarf2_debug *stash;
  struct comp_unit *unit;
  htab_t sym_hash;
  bfd_signed_vma result = 0;
  asymbol **psym;
  int found = 0;

  if (symbols == NULL || pinfo == NULL)
    return 0;

  stash = (struct dwarf2_debug *) *pinfo;
  if (stash == NULL)
    return 0;

  sym_hash = htab_create_alloc (10, hash_asymbol, eq_asymbol, NULL, xcalloc, free);
  if (sym_hash == NULL)
    return 0;

  for (psym = symbols; *psym != NULL; psym++)
    {
      asymbol *sym = *psym;

      if ((sym->flags & BSF_FUNCTION) && sym->section != NULL)
        {
          void **slot = htab_find_slot (sym_hash, sym, INSERT);
          if (slot != NULL)
            *slot = sym;
        }
    }

  for (unit = stash->f.all_comp_units; unit != NULL && !found; unit = unit->next_unit)
    {
      struct funcinfo *func;

      comp_unit_maybe_decode_line_info (unit);

      for (func = unit->function_table; func != NULL; func = func->prev_func)
        if (func->name && func->arange.low)
          {
            asymbol search = { 0 };
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

  htab_delete (sym_hash);
  return result;
}

/* See _bfd_dwarf2_find_nearest_line_with_alt.  */

int _bfd_dwarf2_find_nearest_line(
    bfd *abfd,
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
    return _bfd_dwarf2_find_nearest_line_with_alt(
        abfd,
        NULL,
        symbols,
        symbol,
        section,
        offset,
        filename_ptr,
        functionname_ptr,
        linenumber_ptr,
        discriminator_ptr,
        debug_sections,
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
  bfd_vma addr = 0;
  struct comp_unit* each;
  struct funcinfo *function = NULL;
  int found = false;
  bool do_line;

  const char *filename_tmp = NULL;
  const char **filename_out = filename_ptr ? filename_ptr : &filename_tmp;
  unsigned int lineno_tmp = 0;
  unsigned int *lineno_out = linenumber_ptr ? linenumber_ptr : &lineno_tmp;
  unsigned int discrim_tmp = 0;
  unsigned int *discrim_out = discriminator_ptr ? discriminator_ptr : &discrim_tmp;

  if (filename_ptr)
    *filename_ptr = NULL;
  if (functionname_ptr != NULL)
    *functionname_ptr = NULL;
  if (linenumber_ptr)
    *linenumber_ptr = 0;
  if (discriminator_ptr)
    *discriminator_ptr = 0;

  if (abfd == NULL || pinfo == NULL)
    return false;

  if (! _bfd_dwarf2_slurp_debug_info (abfd, NULL, debug_sections,
				      symbols, pinfo,
				      (abfd->flags & (EXEC_P | DYNAMIC)) == 0))
    return false;

  stash = (struct dwarf2_debug *) *pinfo;
  if (stash == NULL)
    return false;

  if (stash->alt.bfd_ptr == NULL && alt_filename != NULL)
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
    }

  do_line = symbol != NULL;
  if (do_line)
    {
      BFD_ASSERT (section == NULL && offset == 0 && functionname_ptr == NULL);
      section = bfd_asymbol_section (symbol);
      if (section == NULL)
        return false;
      addr = symbol->value;
    }
  else
    {
      BFD_ASSERT (section != NULL && functionname_ptr != NULL);
      if (section == NULL)
        return false;
      addr = offset;

      if (symbols != NULL && (section->flags & SEC_CODE) == 0)
	{
	  asymbol **tmp;

	  for (tmp = symbols; (*tmp) != NULL; ++tmp)
	    if ((*tmp)->the_bfd == abfd
		&& (*tmp)->section == section
		&& (*tmp)->value == offset
		&& ((*tmp)->flags & BSF_SECTION_SYM) == 0)
	      {
		symbol = *tmp;
		do_line = true;
		if ((symbol->flags & BSF_GLOBAL) != 0)
		  break;
	      }
	}
    }

  if (section != NULL)
    {
      if (section->output_section)
	addr += section->output_section->vma + section->output_offset;
      else
	addr += section->vma;
    }

  if (! stash->f.info_ptr)
    return false;

  stash->inliner_chain = NULL;

  if (do_line)
    {
      if (stash->info_hash_status == STASH_INFO_HASH_OFF)
	stash_maybe_enable_info_hash_tables (abfd, stash);

      if (stash->info_hash_status == STASH_INFO_HASH_ON)
	stash_maybe_update_info_hash_tables (stash);

      if (stash->info_hash_status == STASH_INFO_HASH_ON)
	{
	  found = stash_find_line_fast (stash, symbol, addr,
					filename_out, lineno_out);
	  if (found)
	    goto done;
	}

      for (each = stash->f.all_comp_units; each; each = each->next_unit)
	if ((symbol->flags & BSF_FUNCTION) == 0
	    || comp_unit_may_contain_address (each, addr))
	  {
	    found = comp_unit_find_line (each, symbol, addr, filename_out,
					 lineno_out);
	    if (found)
	      goto done;
	  }
    }
  else
    {
      struct trie_node *trie = stash->f.trie_root;
      unsigned int bits = VMA_BITS - 8;
      struct comp_unit **prev_each;

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

	      found = comp_unit_find_nearest_line (unit, addr,
						   filename_out,
						   &function,
						   lineno_out,
						   discrim_out);
	      if (found)
		goto done;
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

	  found = comp_unit_find_nearest_line (each, addr,
					       filename_out,
					       &function,
					       lineno_out,
					       discrim_out);
	  if (found)
	    goto done;
	  prev_each = &each->next_unit_without_ranges;
	}
    }

  while ((each = stash_comp_unit (stash, &stash->f)) != NULL)
    {
      if (do_line)
	found = (((symbol->flags & BSF_FUNCTION) == 0
		  || comp_unit_may_contain_address (each, addr))
		 && comp_unit_find_line (each, symbol, addr,
					 filename_out, lineno_out));
      else
	found = (comp_unit_may_contain_address (each, addr)
		 && comp_unit_find_nearest_line (each, addr,
						 filename_out,
						 &function,
						 lineno_out,
						 discrim_out));

      if (found)
	break;
    }

 done:
  if (functionname_ptr && function && function->is_linkage)
    {
      *functionname_ptr = function->name;
      if (!found)
        found = 2;
    }
  else if (functionname_ptr
	   && (!*functionname_ptr
	       || (function && !function->is_linkage)))
    {
      asymbol *fun;
      asymbol **syms = symbols;
      asection *sec = section;

      _bfd_dwarf2_stash_syms (stash, abfd, &sec, &syms);
      fun = _bfd_elf_find_function (abfd, syms, sec, offset,
				    *filename_out ? NULL : filename_out,
				    functionname_ptr);

      if (!found && fun != NULL)
	found = 2;

      if (function && !function->is_linkage)
	{
	  bfd_vma sec_vma = section ? section->vma : 0;

	  if (section && section->output_section != NULL)
	    sec_vma = section->output_section->vma + section->output_offset;
	  if (fun == NULL)
	    *functionname_ptr = function->name;
	  else if (fun->value + sec_vma == function->arange.low)
	    function->name = *functionname_ptr;
	  function->is_linkage = true;
	}
    }

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
  struct dwarf2_debug *stash;
  struct funcinfo *func;
  const char *filename;
  const char *functionname;
  unsigned int linenumber;

  if (pinfo == NULL)
    return false;

  stash = (struct dwarf2_debug *) *pinfo;
  if (stash == NULL)
    return false;

  func = stash->inliner_chain;
  if (func == NULL || func->caller_func == NULL)
    return false;

  filename = func->caller_file;
  functionname = func->caller_func->name;
  linenumber = func->caller_line;

  if (filename_ptr)
    *filename_ptr = filename;
  if (functionname_ptr)
    *functionname_ptr = functionname;
  if (linenumber_ptr)
    *linenumber_ptr = linenumber;

  stash->inliner_chain = func->caller_func;
  return true;
}

static void cleanup_comp_units(struct dwarf2_debug_file *file)
{
  struct comp_unit *each;

  for (each = file->all_comp_units; each; each = each->next_unit)
    {
      struct funcinfo *function_table = each->function_table;
      struct varinfo *variable_table = each->variable_table;

      if (each->line_table && each->line_table != file->line_table)
        {
          free (each->line_table->files);
          free (each->line_table->dirs);
        }

      free (each->lookup_funcinfo_table);
      each->lookup_funcinfo_table = NULL;

      for (; function_table; function_table = function_table->prev_func)
        {
          free (function_table->file);
          function_table->file = NULL;
          free (function_table->caller_file);
          function_table->caller_file = NULL;
        }

      for (; variable_table; variable_table = variable_table->prev_var)
        {
          free (variable_table->file);
          variable_table->file = NULL;
        }
    }
}

static void cleanup_dwarf2_file(struct dwarf2_debug_file *file)
{
  if (file == NULL)
    return;

  cleanup_comp_units (file);

  if (file->line_table)
    {
      free (file->line_table->files);
      free (file->line_table->dirs);
    }
  if (file->abbrev_offsets)
    htab_delete (file->abbrev_offsets);
  if (file->comp_unit_tree)
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

void
_bfd_dwarf2_cleanup_debug_info (bfd *abfd, void **pinfo)
{
  struct dwarf2_debug *stash;

  (void) abfd;

  if (pinfo == NULL)
    return;

  stash = (struct dwarf2_debug *) *pinfo;
  if (stash == NULL)
    return;

  if (stash->varinfo_hash_table)
    bfd_hash_table_free (&stash->varinfo_hash_table->base);
  if (stash->funcinfo_hash_table)
    bfd_hash_table_free (&stash->funcinfo_hash_table->base);

  cleanup_dwarf2_file (&stash->f);
  cleanup_dwarf2_file (&stash->alt);

  free (stash->sec_vma);
  free (stash->adjusted_sections);
  if (stash->close_on_cleanup && stash->f.bfd_ptr)
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
better_fit(elf_find_function_cache *cache,
           asymbol *sym,
           bfd_vma code_off,
           bfd_size_type code_size,
           bfd_vma offset)
{
  if (cache == NULL || cache->func == NULL || sym == NULL)
    return false;

  const bfd_vma cache_off = cache->code_off;
  const bfd_size_type cache_size = cache->code_size;

  if (code_off > offset)
    return false;

  if (code_off != cache_off)
    return code_off > cache_off;

  if (!(cache_off <= offset && (offset - cache_off) < (bfd_vma) cache_size))
    return code_size > cache_size;

  if (!(code_off <= offset && (offset - code_off) < (bfd_vma) code_size))
    return false;

  {
    flagword cache_flags = cache->func->flags;
    flagword sym_flags = sym->flags;

    if ((cache_flags & BSF_FUNCTION) && ((sym_flags & BSF_FUNCTION) == 0))
      return false;
    if ((sym_flags & BSF_FUNCTION) && ((cache_flags & BSF_FUNCTION) == 0))
      return true;
  }

  {
    const elf_symbol_type *cache_esym = (const elf_symbol_type *) cache->func;
    const elf_symbol_type *sym_esym = (const elf_symbol_type *) sym;

    int cache_type = ELF_ST_TYPE(cache_esym->internal_elf_sym.st_info);
    int sym_type = ELF_ST_TYPE(sym_esym->internal_elf_sym.st_info);

    if (cache_type == STT_NOTYPE && sym_type != STT_NOTYPE)
      return true;
    if (cache_type != STT_NOTYPE && sym_type == STT_NOTYPE)
      return false;
  }

  return code_size < cache_size;
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

  if (elf_tdata (abfd) == NULL)
    return NULL;

  elf_find_function_cache **pcache = &elf_tdata (abfd)->elf_find_function_cache;
  elf_find_function_cache *cache = *pcache;

  if (cache == NULL)
    {
      cache = bfd_zalloc (abfd, sizeof (*cache));
      *pcache = cache;
      if (cache == NULL)
        return NULL;
    }

  {
    int need_refresh = 0;
    if (cache->last_section != section || cache->func == NULL)
      {
        need_refresh = 1;
      }
    else
      {
        bfd_vma start = cache->func->value;
        bfd_vma end = start + cache->code_size;
        if (offset < start)
          need_refresh = 1;
        else if (end < start || offset >= end)
          need_refresh = 1;
      }

    if (need_refresh)
      {
        asymbol *file = NULL;
        asymbol **p;
        enum { nothing_seen, symbol_seen, file_after_symbol_seen } state;
        const struct elf_backend_data *bed = get_elf_backend_data (abfd);

        if (bed == NULL || bed->maybe_function_sym == NULL)
          return NULL;

        state = nothing_seen;
        cache->filename = NULL;
        cache->func = NULL;
        cache->code_size = 0;
        cache->code_off = 0;
        cache->last_section = section;

        for (p = symbols; *p != NULL; p++)
          {
            asymbol *sym = *p;
            bfd_vma code_off;
            bfd_size_type size;

            if ((sym->flags & BSF_FILE) != 0)
              {
                file = sym;
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

                if (file != NULL
                    && ((sym->flags & BSF_LOCAL) != 0
                        || state != file_after_symbol_seen))
                  cache->filename = bfd_asymbol_name (file);
              }
            else
              {
                if (code_off > offset && code_off > cache->code_off)
                  {
                    bfd_vma end = cache->code_off + cache->code_size;
                    if (end > cache->code_off && code_off < end)
                      cache->code_size = code_off - cache->code_off;
                  }
              }
          }
      }
  }

  if (cache->func == NULL)
    return NULL;

  if (filename_ptr)
    *filename_ptr = cache->filename;
  if (functionname_ptr)
    *functionname_ptr = bfd_asymbol_name (cache->func);

  return cache->func;
}
