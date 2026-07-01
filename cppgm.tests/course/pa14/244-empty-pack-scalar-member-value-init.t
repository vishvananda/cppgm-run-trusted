template<typename... Args>
struct Box {
  int value;
  Box(Args... args) : value(args...) {}
};

int main() {
  Box<> box;
  return box.value;
}
