int destroyed;

template<typename T>
struct Box {
  T value;
  Box() : value() {}
  Box(Box&& other) : value(other.value) { other.value = 0; }
  Box& operator=(Box&& other) {
    value = other.value;
    other.value = 0;
    return *this;
  }
  ~Box() { destroyed = destroyed + 1; }
};

Box<int> make_box();

int main() {
  Box<int> box;
  box = make_box();
  return 0;
}
