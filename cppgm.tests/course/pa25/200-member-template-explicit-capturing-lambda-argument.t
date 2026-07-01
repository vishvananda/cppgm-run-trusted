struct C {
  int bias;

  C() : bias(5) {}

  template <class R, class F>
  R call(const F & f)
  {
    return f(2);
  }

  int run()
  {
    return call<int>([this](int x) -> int { return bias + x; });
  }
};

int main()
{
  C c;
  return c.run() - 7;
}
