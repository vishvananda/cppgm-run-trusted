// VALIDATION: run-pass
// Regression: function-pointer non-type template arguments must not leak raw
// binding addresses into record, RTTI, or vtable LowIR symbols.

template<int (*F)(int)>
struct S
{
  virtual int run(int x)
  {
    return F(x);
  }
};

int square(int x)
{
  return x * x;
}

int main()
{
  S<square> s;
  return s.run(5) == 25 ? 0 : 1;
}
