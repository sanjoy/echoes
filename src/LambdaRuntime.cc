#include <cassert>
#include <cstdint>
#include <memory>
#include <sstream>
#include <stdexcept>

using namespace std;

static void die(const char *errorstr) __attribute__((noreturn));

static void die(const char *errorstr) {
  printf("fatal error: %s\n", errorstr);
  abort();
}

class value;
class closure_value;
typedef shared_ptr<value> (function_t) (const closure_value *);

class value {
 protected:
  value(int kind) : kind_(kind) { }

 public:
  bool is_int_value() const { return kind_ == kIntValue; }
  bool is_bool_value() const { return kind_ == kBoolValue; }
  bool is_closure_value() const { return kind_ == kClosureValue; }

  string to_string() const;

 protected:
  enum {
    kIntValue,
    kBoolValue,
    kClosureValue
  };

 private:
  int kind_;
};

class closure_value : public value {
 public:
  closure_value(function_t *body, int size)
      : value(value::kClosureValue),
        body_(body),
        size_(size),
        param_index_(0) {
    params_ = new shared_ptr<value>[size_];
  }

  closure_value(const closure_value &) = delete;
  void operator=(const closure_value &) = delete;

  shared_ptr<value> push(shared_ptr<value> new_param) {
    if (param_index_ == size_) {
      die("too many pushes!");
    }

    shared_ptr<closure_value> new_closure =
        make_shared<closure_value>(body_, size_);
    copy(params_, &params_[param_index_], new_closure->params_);
    new_closure->param_index_ = param_index_;
    new_closure->params_[new_closure->param_index_++] = new_param;

    if (param_index_ == (size_ - 1)) {
      return new_closure->body_(new_closure.get());
    } else {
      return new_closure;
    }
  }

  shared_ptr<value> at(int index) const {
    assert(index < param_index_);
    assert(index < size_);
    return params_[index];
  }

  string to_string() const {
    return "[closure]";
  }

  ~closure_value() {
    delete []params_;
  }

 private:
  function_t *body_;
  int size_;
  int param_index_;

  shared_ptr<value> *params_;
};

class int_value : public value {
 public:
  explicit int_value(int64_t int_value)
      : value(kIntValue),
        int_value_(int_value) { }

  int64_t get_int_value() const { return int_value_; }

  string to_string() const {
    stringstream s;
    s << int_value_;
    return s.str();
  }

 private:
  int64_t int_value_;
};

class bool_value : public value {
 public:
  explicit bool_value(bool bool_value)
  : value(kBoolValue),
    bool_value_(bool_value) { }

  bool get_bool_value() const { return bool_value_; }

  string to_string() const {
    return bool_value_ ? "true" : "false";
  }

 private:
  bool bool_value_;
};

string value::to_string() const {
  switch (kind_) {
    case kClosureValue:
      return static_cast<const closure_value *>(this)->to_string();

    case kBoolValue:
      return static_cast<const bool_value *>(this)->to_string();

    case kIntValue:
      return static_cast<const int_value *>(this)->to_string();
  }

  die("unknown value type!");
}

#define GENERIC_CAST(what, type)                \
  ({                                            \
    if (!(what)->is_ ## type()) {               \
      die("expected " #type "!");               \
    }                                           \
    static_pointer_cast<type, value>(what);     \
  })

#define CAST_TO_CLOSURE(what) GENERIC_CAST(what, closure_value)
#define CAST_TO_INT(what) GENERIC_CAST(what, int_value)
#define CAST_TO_BOOL(what) GENERIC_CAST(what, bool_value)

#define MAKE_CLOSURE(body) make_shared<closure_value>(body, body ## _FrameSize)
#define MAKE_BOOL(lit) make_shared<bool_value>(lit)
#define MAKE_INT(lit) make_shared<int_value>(lit)

#define GENERIC_BIN_OP(x, y, op, result_type)                   \
  MAKE_ ## result_type(CAST_TO_INT(x)->get_int_value() op       \
                       CAST_TO_INT(y)->get_int_value())

#define BIN_PLUS(x, y) GENERIC_BIN_OP(x, y, +, INT)
#define BIN_MINUS(x, y) GENERIC_BIN_OP(x, y, -, INT)
#define BIN_MULT(x, y) GENERIC_BIN_OP(x, y, *, INT)
#define BIN_DIV(x, y) ({                                        \
      int y_evaluated = CAST_TO_INT(y)->get_int_value();        \
      if (y_evaluated == 0) {                                   \
        die("division by zero!");                               \
      }                                                         \
      MAKE_INT(CAST_TO_INT(x)->get_int_value() / y_evaluated);  \
    })

#define BIN_LT(x, y) GENERIC_BIN_OP(x, y, <, BOOL)
#define BIN_EQ(x, y) GENERIC_BIN_OP(x, y, ==, BOOL)

#include SOURCE

int main() {
  shared_ptr<closure_value> null_closure;
  printf("result : %s\n", epoch(nullptr)->to_string().c_str());
}
