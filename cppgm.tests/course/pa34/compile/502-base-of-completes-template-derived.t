struct Base {};

template<class T>
struct DerivedTemplate : Base {};

static_assert(__is_base_of(Base, DerivedTemplate<int>),
              "__is_base_of should complete derived class template bases");

int main() {
  return 0;
}
