#if !__has_builtin(__builtin_memset)
#error expected __builtin_memset
#endif

void *fill(char *buf, unsigned long n) {
  return __builtin_memset(buf, 0x5a, n);
}

int main() {
  char buf[8];
  return fill(buf, sizeof(buf)) == buf ? 0 : 1;
}
