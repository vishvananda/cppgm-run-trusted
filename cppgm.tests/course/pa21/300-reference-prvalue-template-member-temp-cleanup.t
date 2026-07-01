struct Iterator {
  static int live;

  Iterator() {
    ++live;
  }

  Iterator(const Iterator&) {
    ++live;
  }

  ~Iterator() {
    --live;
  }
};

int Iterator::live = 0;

template<class It, class Alloc>
struct AssignRange {
  It first;
  It last;
  Alloc& alloc;

  AssignRange(const It& f, const It& l, Alloc& a)
    : first(f), last(l), alloc(a) {}

  void operator()(int*) const {}
};

template<class It, class Alloc>
AssignRange<It, Alloc> make_assign_range(const It& first,
                                         const It& last,
                                         Alloc& alloc) {
  return AssignRange<It, Alloc>(first, last, alloc);
}

struct Buffer {
  int alloc;

  Buffer() : alloc(0) {}

  Iterator begin() {
    return Iterator();
  }

  Iterator end() {
    return Iterator();
  }

  template<class Functor>
  void assign_n(int, int, const Functor& fnc) {
    fnc(0);
  }

  template<class It>
  void assign(It first, It last) {
    assign_n(1, 1, make_assign_range(first, last, alloc));
  }
};

int main() {
  Buffer buffer;
  buffer.assign(buffer.begin(), buffer.end());
  return Iterator::live;
}
