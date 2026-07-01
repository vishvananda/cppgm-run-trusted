int below_int_min(long value)
{
  return value < (-2147483647 - 1) ? 1 : 0;
}

int main()
{
  return below_int_min(0);
}
