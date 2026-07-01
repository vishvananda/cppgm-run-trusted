struct R {
  R();
  R(const R&);
  ~R();
};

bool cond();
R make();

void f() {
  R live;
  R x = cond() ? make() : R();
}
