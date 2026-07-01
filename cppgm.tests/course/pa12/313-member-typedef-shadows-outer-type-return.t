namespace std {
struct iterator {
  int unused;
};

struct BitIterator {
  typedef BitIterator iterator;

  iterator self() const {
    return *this;
  }
};
}
