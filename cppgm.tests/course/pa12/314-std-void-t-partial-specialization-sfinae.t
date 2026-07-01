namespace std {
template<class T>
struct remove_reference {
  typedef T type;
};

template<class...>
using __void_t = void;
}

template<class T, class D>
struct Outer {
  template<class U, class E, class = void>
  struct Ptr {
    typedef U* type;
  };

  template<class U, class E>
  struct Ptr<U, E, std::__void_t<typename std::remove_reference<E>::type::pointer> > {
    typedef typename std::remove_reference<E>::type::pointer type;
  };

  typedef typename Ptr<T, D>::type pointer;
};

struct Entity {};

template<class T>
struct DefaultDelete {};

Outer<Entity, DefaultDelete<Entity> >::pointer make_pointer() {
  return 0;
}
