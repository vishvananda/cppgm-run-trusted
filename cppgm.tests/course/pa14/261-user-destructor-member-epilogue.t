int destroyed;

struct Member
{
  ~Member()
  {
    destroyed = destroyed + 1;
  }
};

struct Owner
{
  Member member;

  ~Owner()
  {
    destroyed = destroyed + 10;
  }
};

int main()
{
  {
    Owner owner;
  }
  return destroyed == 11 ? 0 : 1;
}
