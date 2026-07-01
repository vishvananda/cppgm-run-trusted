struct S {
  long a;
  long b;
};

S make();
bool cond();

int main() {
  S s = cond() ? make() : S();
  return s.a == 0 && s.b == 0 ? 0 : 1;
}
