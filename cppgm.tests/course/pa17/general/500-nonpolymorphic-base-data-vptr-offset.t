struct Base {
  int value;
  Base() : value(3) {}
  int get() { return value; }
};

struct Derived : Base {
  virtual int dispatch() { return get(); }
};

int via_ptr(Derived *d) {
  Base *b = d;
  return b->get();
}

int via_ref(Derived &d) {
  Base &b = d;
  return b.get();
}

int main() {
  Derived d;
  return d.dispatch() + via_ptr(&d) + via_ref(d) - 9;
}
