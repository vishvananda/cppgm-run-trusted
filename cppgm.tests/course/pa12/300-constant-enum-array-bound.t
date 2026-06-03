enum E {
  A = 2,
  B = A + 3
};

int main() {
  int values[B];
  return __builtin_constant_p(B) + sizeof(values);
}
