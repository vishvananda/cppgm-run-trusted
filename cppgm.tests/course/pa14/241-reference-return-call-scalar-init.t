struct Box {
  unsigned int value;
  unsigned int& at() { return value; }
};

void fill(Box& box) {
  box.value = 0x61;
}

int main() {
  Box box;
  fill(box);
  unsigned int cp = box.at();
  return cp == 0x61 ? 0 : 2;
}
