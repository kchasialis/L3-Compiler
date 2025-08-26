#include "memory.h"
#include "lwlog.h"
#include "fail.h"
#include "block_header.h"
#include "address.h"

#define FREE_LIST_COUNT 32
#define MIN_BLOCK_SIZE (1)
#define BLOCK_NULL (0)
#define FP1_OFFSET (258)
#define FP2_OFFSET (517)

// Memory layout is as follows:
// - code area
// - bitmap
// - heap area
struct memory {
    value_t *mem_start;
    value_t *mem_end;

    value_t *bitmap;
    uint32_t bitmap_size;

    value_t *heap_start;

    value_t *free_lists[FREE_LIST_COUNT];
};

/* Bitmap operations.  */
void bitmap_set(value_t *bitmap, size_t block_idx) {
    uint32_t bitmap_idx = block_idx / 32;
    uint32_t bit_idx = block_idx % 32;

    bitmap[bitmap_idx] |= (1U << bit_idx);
}

void bitmap_clear(value_t *bitmap, size_t block_idx) {
    uint32_t bitmap_idx = block_idx / 32;
    uint32_t bit_idx = block_idx % 32;

    bitmap[bitmap_idx] &= ~(1U << bit_idx);
}

int bitmap_get(value_t *bitmap, size_t block_idx) {
    uint32_t bitmap_idx = block_idx / 32;
    uint32_t bit_idx = block_idx % 32;

    return (bitmap[bitmap_idx] & (1U << bit_idx)) != 0;
}

int is_heap_addr(memory *self, const value_t *addr) {
    return self->heap_start <= addr && addr < self->mem_end;
}

static inline size_t max(size_t a, size_t b) {
return a > b ? a : b;
}

// Returns the index of the list that should be used for a block of size `size`.
value_t b2i(memory *self, value_t *block) {
    if (!block) {
        return BLOCK_NULL;
    }

    // IN WORDS
    return block - self->heap_start;
}

size_t calculate_new_size(memory *self, value_t *block) {
    size_t block_sz = max(block_size(block), 1);
    value_t *next_block = block + block_sz + HEADER_SIZE;
    while (is_heap_addr(self, next_block) && block_tag(next_block) == tag_FreeBlock) {
        size_t next_block_sz = max(block_size(next_block), 1);
        block_sz += next_block_sz + HEADER_SIZE;
        next_block += next_block_sz + HEADER_SIZE;
    }

    return block_sz;
}


value_t *block_next(memory *self, value_t *block) {
    if (block[0] == BLOCK_NULL) {
        return NULL;
    }

    value_t *next = self->heap_start + block[0];
    return next;
}

size_t list_index(size_t size) {
    if (size >= FREE_LIST_COUNT) {
        return 0;
    }

    return size;
}

void set_next_index(value_t *block, value_t index) {
    block[0] = index;
}

void set_next_block(memory *self, value_t *block, value_t *next) {
    set_next_index(block, b2i(self, next));
}

value_t *find_block(memory *self, value_t size) {
    size_t index = list_index(size);
    if (index != 0) {
        value_t *block = self->free_lists[index];
        if (block) {
            return block;
        }
    }

    // Now we need to find a block in the last list.
    value_t *head = self->free_lists[0];
    /* Find a block but make sure it can be split further if exact size is not found. */
    while (head) {
        size_t b_size = block_size(head);
        if (b_size == size) {
            return head;
        }
        // Make sure it can be split further.
        if (b_size >= size + MIN_BLOCK_SIZE + HEADER_SIZE) {
            return head;
        }
        head = block_next(self, head);
    }

    return NULL;
}

void detach_block(memory *self, value_t *block, size_t b_size) {
    size_t index = list_index(b_size);

    /* Find the block in the free list */
    value_t *head = self->free_lists[index];
    value_t *prev = NULL;
    while (head) {
        if (head == block) {
            break;
        }
        prev = head;
        head = block_next(self, head);
    }

    if (prev) {
        set_next_block(self, prev, block_next(self, block));
    } else {
        self->free_lists[index] = block_next(self, block);
    }
}

void attach_block(memory *self, value_t *block, size_t b_size) {
    size_t index = list_index(b_size);
    value_t *head = self->free_lists[index];

    // If there is no head, the block becomes the head
    if (!head) {
        set_next_index(block, BLOCK_NULL);

        self->free_lists[index] = block;

        return;
    }

    // Otherwise, the block becomes the new head
    set_next_block(self, block, head);
    self->free_lists[index] = block;
}

value_t* allocate_implementation(memory *self, tag_t tag, value_t size, value_t *block_found) {
    size_t b_size = max(block_size(block_found), 1);

    detach_block(self, block_found, b_size);
    block_set_tag_size(block_found, tag, size);
    // Mark it as allocated.
    bitmap_set(self->bitmap, b2i(self, block_found));

    // Case 1: block is exactly the size we need.
    // Block is either exactly the size or 0.
    if (b_size == size || (size == 0 && b_size == 1)) {
        return block_found;
    }

    // Case 2: block is bigger than we need.
    size = max(size, 1);
    int remaining_size = b_size - size - HEADER_SIZE;

    // Split the block.
    value_t *remaining_block = block_found + size + HEADER_SIZE;
    block_set_tag_size(remaining_block, tag_FreeBlock, remaining_size);
    bitmap_clear(self->bitmap, b2i(self, remaining_block));
    // Insert the remaining block to the free list.
    attach_block(self, remaining_block, remaining_size);

    return block_found;
}

void coalesce(memory *self) {
    // Clear the free lists.
    for (size_t i = 0; i < FREE_LIST_COUNT; i++) {
        self->free_lists[i] = NULL;
    }

    value_t *current_block = &self->heap_start[HEADER_SIZE];
    while (is_heap_addr(self, current_block)) {
        if (block_tag(current_block) != tag_FreeBlock) {
            current_block += max(block_size(current_block), 1) + HEADER_SIZE;
            continue;
        }

        size_t new_size = calculate_new_size(self, current_block);
        block_set_tag_size(current_block, tag_FreeBlock, new_size);
        attach_block(self, current_block, new_size);
        current_block += new_size + HEADER_SIZE;
    }
}

void walky_rooty(memory *self, value_t fp) {
    if ((fp & 0b11) != 0) {
        return;
    }

    value_t *phys_fp = addr_v_to_p(self->mem_start, fp);

    value_t *fp_index1 = (value_t *) self->bitmap - FP1_OFFSET;
    value_t *fp_index2 = (value_t *) self->bitmap - FP2_OFFSET;

    if (is_heap_addr(self, phys_fp)) {
        size_t block_idx = b2i(self, phys_fp);
        if (bitmap_get(self->bitmap, block_idx)) {
            bitmap_clear(self->bitmap, block_idx);
            // walk the block
            size_t size = block_size(phys_fp);
            for (size_t i = 0; i < size; i++) {
                walky_rooty(self, phys_fp[i]);
            }
        }
    } else {
        if (phys_fp == fp_index1 || phys_fp == fp_index2) {
            size_t size = block_size(phys_fp);
            for (size_t i = 0; i < size; i++) {
                walky_rooty(self, phys_fp[i]);
            }
        }
    }
}

void fix_bitmap(memory *self) {
    value_t *block_start = &self->heap_start[HEADER_SIZE];
    while (is_heap_addr(self, block_start)) {
        size_t block_sz = max(block_size(block_start), 1);
        if (block_tag(block_start) != tag_FreeBlock) {
            bitmap_set(self->bitmap, b2i(self, block_start));
        }

        block_start += block_sz + HEADER_SIZE;
    }
}

void mark_and_sweep(memory *self, value_t *root) {
    // Mark phase
    size_t size = block_size(root);
    for (size_t i = 0; i < size; i++) {
        walky_rooty(self, root[i]);
    }

    // Sweep phase
    value_t *current_block = &self->heap_start[HEADER_SIZE];
    /* Iterate over the blocks.  */
    while (is_heap_addr(self, current_block)) {
        size_t block_idx = b2i(self, current_block);
        if (bitmap_get(self->bitmap, block_idx)) {
            memory_free_block(self, current_block);
        }
        current_block += max(block_size(current_block), 1) + HEADER_SIZE;
    }

    fix_bitmap(self);
}

// Returns a string identifying the memory module.
char* memory_get_identity(void) {
    return "wham GC (memory is freed by sweeping)";
}

// Create a memory module with `total_byte_size` memory.
memory* memory_new(size_t total_byte_size) {
    value_t* memory_start = calloc(1, total_byte_size);
    if (!memory_start) {
        fail("cannot allocate %zd bytes of memory", total_byte_size);
    }
    value_t* memory_end = memory_start + (total_byte_size / sizeof(value_t));

    memory* self = calloc(1, sizeof(memory));
    if (!self) fail("cannot allocate memory");
    self->mem_start = memory_start;
    self->mem_end = memory_end;

    for (size_t i = 0; i < FREE_LIST_COUNT; i++) {
        self->free_lists[i] = NULL;
    }

    return self;
}

// Release the memory module.
void memory_free(memory* self) {
    free(self->mem_start);
    free(self);
}

// Get the address of the beginning of the memory area.
value_t* memory_get_start(memory* self) {
    return self->mem_start;
}

// Get the address just after the end of the memory area.
value_t* memory_get_end(memory* self) {
    return self->mem_end;
}

// Set the heap start, following the code area.
void memory_set_heap_start(memory* self, value_t* heap_start) {

    // addressable blocks are 4 bytes, end - start
    size_t heap_size_in_words = (memory_get_end(self) - heap_start);

    // each byte can hold 8 blocks
    size_t bitmap_size = ((heap_size_in_words + 31) / 32);

    // set the bitmap
    self->bitmap = heap_start;
    self->bitmap_size = bitmap_size;
    self->heap_start = heap_start + bitmap_size;

    // create one big memory block for the entire list
    // Size is in words!
    value_t *block = &self->heap_start[HEADER_SIZE];
    heap_size_in_words -= self->bitmap_size;
    block_set_tag_size(block, tag_FreeBlock, heap_size_in_words - HEADER_SIZE);

    // assert block is at least 3 words
    if (heap_size_in_words < 2) {
        fail("The VM needs at least 2 words to work!");
    }

    // Set next and previous block to NULL
    set_next_index(block, BLOCK_NULL);

    // insert to free list
    self->free_lists[list_index(heap_size_in_words)] = block;
}

// Allocate a block with the given `tag` and `size`, using `root` (the
// frame pointer) in case garbage collection has to be performed.
value_t* memory_allocate(memory* self, tag_t tag, value_t size, value_t* root) {
    value_t *block = find_block(self, max(size, 1));
    if (block) {
        block = allocate_implementation(self, tag, size, block);
        return block;
    }

    mark_and_sweep(self, root);
    coalesce(self);

    block = find_block(self, max(size, 1));
    if (block) {
        block = allocate_implementation(self, tag, size, block);
        return block;
    }

    fail("Out of memory, cannot allocate block of size %u", size);
    return NULL;
}

// Copy `block` in a newly-allocated block, using `root` (the frame
// pointer) in case garbage collection has to be performed.
value_t* memory_copy_of_block(memory* self, value_t* block, value_t* root) {
    tag_t tag = block_tag(block);
    value_t size = block_size(block);
    value_t* copy = memory_allocate(self, tag, size, root);
    memcpy(copy, block, size * sizeof(value_t));
    return copy;
}

// Free `block` (without having to wait for next garbage collection).
void memory_free_block(memory* self, value_t* block) {
    if (!is_heap_addr(self, block)) {
        lwlog_emerg("Attempting to free a block %p that is out of bounds!", block);
        return;
    }

    bitmap_clear(self->bitmap, b2i(self, block));

    size_t size = block_size(block);
    block_set_tag_size(block, tag_FreeBlock, size);

    attach_block(self, block, max(size, 1));
}
