struct S {
  int x;
  S(int v) : x(v) {}
  S() : S(7) {}
};

int main() {
  S s;
  return s.x;
}
