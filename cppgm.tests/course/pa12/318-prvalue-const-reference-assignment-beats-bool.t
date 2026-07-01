struct RefProxy {};

struct Boolish {
  Boolish(RefProxy);
};

RefProxy make_ref_proxy();
int choose(const RefProxy&);
long choose(Boolish);

typedef decltype(choose(make_ref_proxy())) Chosen;
