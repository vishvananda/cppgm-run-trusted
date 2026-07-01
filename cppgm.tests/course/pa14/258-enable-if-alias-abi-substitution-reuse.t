template<bool B, class T = void>
struct enable_if {
};

template<class T>
struct enable_if<true, T> {
  typedef T type;
};

template<bool B, class T = void>
using __enable_if_t = typename enable_if<B, T>::type;

template<class T>
struct same_type {
  static const bool value = true;
};

template<class T>
struct Iter {
};

struct Tree {
  template<class It>
  __enable_if_t<same_type<It>::value, void> insert(It first, It last) {
    (void)first;
    (void)last;
  }

  template<class It>
  typename enable_if<same_type<It>::value, void>::type insert_resolved(It first, It last) {
    (void)first;
    (void)last;
  }
};

int main() {
  Tree tree;
  Iter<int> it;
  tree.insert(it, it);
  tree.insert_resolved(it, it);
  return 0;
}
