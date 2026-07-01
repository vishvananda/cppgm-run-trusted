const char * const paths[] = { 0, "ok" };

int main()
{
  return paths[0] == 0 && paths[1][0] == 'o' ? 0 : 1;
}
