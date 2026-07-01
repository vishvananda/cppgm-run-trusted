struct C {
  template <class R, class F>
  R call(const F & f)
  {
    return f(2);
  }

  int run()
  {
    return call<int>([](int x) -> int { return x + 5; });
  }
};

int main()
{
  C c;
  return c.run() - 7;
}
