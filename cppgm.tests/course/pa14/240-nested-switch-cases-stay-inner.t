int main() {
  int x = 0;
  int y = 1;
  switch (x) {
    case 0:
      switch (y) {
        case 1:
          return 0;
        default:
          return 1;
      }
    default:
      return 2;
  }
  return 3;
}
