#ifndef __ECHOES_RUNTIME_H
#define __ECHOES_RUNTIME_H

/*  We don't really _need_ a header specifying the dependencies right
 *  now; but it is nice to have the interface in a separate
 *  header.  */

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

typedef intptr_t value_t;
typedef intptr_t word_t;

typedef value_t (*closure_function_t) (value_t *);

typedef struct {
  closure_function_t callee;
  word_t arg_count;
} clsr_base_node_t;

typedef struct {
  value_t next;
  word_t args_left;
  value_t this_arg;
} clsr_app_node_t;

typedef struct memory_chunk memory_chunk_t;

struct memory_chunk {
  memory_chunk_t *next;
  size_t size;
  uint8_t begin[0];
};

typedef struct {
  word_t header;
  word_t gc_loc;
  word_t gc_lim;

  memory_chunk_t *chunk;
} globals_t;

typedef enum {
  kTypeInteger,
  kTypeBoolean,
  kTypeClsrBase,
  kTypeClsrApp,
  kTypeInvalid
} value_type_t;

static inline value_type_t value_get_type(value_t value) {
  switch (value & 3) {
    case 0:
      return kTypeInteger;
    case 2:
      return kTypeBoolean;
    case 1:
      return kTypeClsrApp;
    case 3:
      return kTypeClsrBase;
  }
  assert(0 && "value & 3 can only have four values!");
  return kTypeInvalid;
}

static clsr_base_node_t *value_to_base_node(value_t value) {
  return (clsr_base_node_t *) (value & ~3);
}

static clsr_app_node_t *value_to_app_node(value_t value) {
  return (clsr_app_node_t *) (value & ~3);
}

clsr_base_node_t *runtime_allocate_base_node(globals_t *);
clsr_app_node_t *runtime_allocate_app_node(globals_t *);
value_t runtime_force(clsr_app_node_t *);

void value_print(value_t, FILE *);

void runtime_panic(const char *string);

value_t epoch(globals_t *);

#endif /* __ECHOES_RUNTIME_H */
