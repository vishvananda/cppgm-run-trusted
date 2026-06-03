int main() {
  int out = 0;
  switch (int x = 1) {
    case 1:
      out = x;
      break;
    default:
      out = 2;
  }
  return out - 1;
}
