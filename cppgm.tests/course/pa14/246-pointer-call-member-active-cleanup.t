struct T {
  int kind;
  int fundamental;
  T() : kind(0), fundamental(18) {}
};

struct P {
  T *p;
  P(T *q) : p(q) {}
  P(const P& other) : p(other.p) {}
  ~P() {}
  T *operator->() const { return p; }
  T *get() const { return p; }
};

bool is_a(P type) {
  return type.get() != 0 && type->kind == 0;
}

int main() {
  T t;
  P p(&t);
  return is_a(p) ? 0 : 1;
}
