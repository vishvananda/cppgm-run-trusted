#if !__has_builtin(__is_invocable)
#error expected __is_invocable
#endif
#if !__has_builtin(__is_invocable_r)
#error expected __is_invocable_r
#endif
#if !__has_builtin(__is_signed)
#error expected __is_signed
#endif

using fn = int (*)(double);

static_assert(__is_invocable(fn, double), "");
static_assert(__is_invocable_r(long, fn, double), "");
static_assert(__is_invocable_r(void, fn, double), "");
static_assert(!__is_invocable_r(int*, fn, double), "");

static_assert(__is_signed(int), "");
static_assert(__is_signed(double), "");
static_assert(!__is_signed(unsigned int), "");
static_assert(!__is_signed(bool), "");

int target(double) {
  return 1;
}

int main() {
  fn f = target;
  return f(1.0);
}
