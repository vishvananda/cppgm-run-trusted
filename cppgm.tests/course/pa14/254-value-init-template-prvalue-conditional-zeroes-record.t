template<class T>
struct S {
  long a;
  long b;
};

S<int> make();
bool cond();

int main() {
  S<int> s = cond() ? make() : S<int>();
  return s.a == 0 && s.b == 0 ? 0 : 1;
}
