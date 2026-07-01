typedef unsigned long size_t;

template<size_t S>
char *keep_array_bound(char (&value)[S])
{
  return value;
}

int main()
{
  char buf[5];
  return keep_array_bound(buf) == buf ? 0 : 1;
}
