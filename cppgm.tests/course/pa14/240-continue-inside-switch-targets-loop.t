int main() {
  int i = 0;
  int n = 0;
  while (i < 3) {
    i = i + 1;
    switch (i) {
      case 1:
        continue;
      default:
        n = n + 1;
    }
    n = n + 10;
  }
  return n;
}
