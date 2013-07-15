#include "runtime.h"

#include <stdlib.h>

#define UNLIKELY(condition) __builtin_expect(condition, 0)

#ifdef VERBOSE
#define LOG(fmt, ...) fprintf(stderr, "log: " fmt "\n", __VA_ARGS__)
#else
#define LOG(...)
#endif

#define kChunkSizeIncrement 50

static inline void *alloc(size_t size, size_t count) {
  void *mem = calloc(size, count);
  if (UNLIKELY(mem == NULL)) {
    fprintf(stderr, "out of memory!");
    abort();
  }
  return mem;
}

static void install_new_memory_chunk(globals_t *globals, size_t size) {
  memory_chunk_t *chunk = alloc(size, 1);
  chunk->next = globals->chunk;
  chunk->size = size;
  globals->gc_loc = (word_t) chunk->begin;
  globals->gc_lim = (word_t) chunk->begin + (size - sizeof(memory_chunk_t));
}

static void *expand_and_allocate(globals_t *globals, size_t size) {
  assert(size < kChunkSizeIncrement && "kChunkSizeIncrement not large enough!");
  install_new_memory_chunk(globals, kChunkSizeIncrement);
  word_t memory = globals->gc_loc;
  globals->gc_loc += size;
  return (void *) memory;
}

clsr_base_node_t *runtime_allocate_base_node(globals_t *globals) {
  return expand_and_allocate(globals, sizeof(clsr_base_node_t));
}

clsr_app_node_t *runtime_allocate_app_node(globals_t *globals) {
  return expand_and_allocate(globals, sizeof(clsr_app_node_t));
}

value_t runtime_force(clsr_app_node_t *root) {
  assert(root->args_left == 0 && "no way can I force this!");

  int argument_count = 1;
  closure_function_t callee = NULL;
  {
    value_t next = root->next;
    while (value_get_type(next) != kTypeClsrBase) {
      assert(value_get_type(next) == kTypeClsrApp);
      next = value_to_app_node(next)->next;
      argument_count ++;
    }
    assert(argument_count == value_to_base_node(next)->arg_count &&
           "invalid force!");
    callee = value_to_base_node(next)->callee;
  }

  value_t *argument_buffer = NULL;
  {
    LOG("allocating %d arguments in argument buffer", argument_count);
    argument_buffer = alloc(sizeof(value_t), argument_count);
    int index = argument_count;

    argument_buffer[--index] = root->this_arg;
    value_t next = root->next;
    while (value_get_type(next) != kTypeClsrBase) {
      assert(value_get_type(next) == kTypeClsrApp);
      argument_buffer[--index] = value_to_app_node(next)->this_arg;
      next = value_to_app_node(next)->next;
    }

    assert(index == 0 && "something went wrong while counting");
  }

  return callee(argument_buffer);
}

void value_print(value_t value, FILE *fptr) {
  switch (value_get_type(value)) {
    case kTypeInteger:
      fprintf(fptr, "int(%d)", (int) value >> 2);
      break;
    case kTypeBoolean:
      fprintf(fptr, "bool(%s)", (value >> 2) ? "true" : "false");
      break;
    case kTypeClsrBase:
      fprintf(fptr, "closure-base(%d)", value_to_base_node(value)->arg_count);
      break;
    case kTypeClsrApp:
      fprintf(fptr, "closure-app(%d)", value_to_app_node(value)->args_left);
      break;
  }
}

void runtime_panic(void) {
  runtime_panic_str("panic!");
}

void runtime_panic_str(const char *string) {
  fprintf(stderr, "internal error: %s\n", string);
  abort();
}

int main() {
  globals_t globals;
  globals.chunk = NULL;
  install_new_memory_chunk(&globals, kChunkSizeIncrement);
  value_print(epoch(&globals), stdout);
  return 0;
}
