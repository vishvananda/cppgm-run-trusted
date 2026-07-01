int f(int x) {
  int first = x + 1;
  bool second = x < 0;
  auto fn = [=]() {
    return second ? first : 0;
  };
  return fn();
}
