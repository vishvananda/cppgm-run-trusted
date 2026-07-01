struct S {
  int x;
};

struct R {
  S& ref;
  R(S& value) : ref(value) {}
};

int main() {
  S s;
  s.x = 3;
  R r(s);
  S* candidate = 0;
  S& selected = candidate ? *candidate : r.ref;
  selected.x = 9;
  return s.x == 9 ? 0 : 1;
}
