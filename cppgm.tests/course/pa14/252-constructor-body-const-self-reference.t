struct S {
  int value;

  S() : value(3) {
  }

  S(const S& other, bool add = true)
    : value(other.value + (add ? 4 : 9)) {
  }
};

int main() {
  S a;
  S b(a);
  return b.value == 7 ? 0 : 1;
}
