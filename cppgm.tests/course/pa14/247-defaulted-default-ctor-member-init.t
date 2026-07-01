struct Inner {
  int x;
  Inner();
  ~Inner();
};

Inner::Inner() : x(7) {}
Inner::~Inner() {}

struct Outer {
  Inner inner;
  Outer() = default;
  ~Outer() = default;
};

int main() {
  Outer outer;
  return outer.inner.x == 7 ? 0 : 1;
}
