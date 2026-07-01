template<class T>
struct Box
{
  struct Guard
  {
    Guard(Box & owner)
      : ref(owner)
    {
    }

    void operator()()
    {
      ref.value += 1;
    }

    Box & ref;
  };

  Box()
    : value(0)
  {
  }

  ~Box()
  {
    Guard(*this)();
  }

  int value;
};

struct Maker
{
  int one()
  {
    struct Piece
    {
      int value;
    };
    Box<Piece> box;
    return box.value;
  }

  int two()
  {
    struct Piece
    {
      int value;
    };
    Box<Piece> box;
    return box.value;
  }
};

int main()
{
  Maker maker;
  return maker.one() == 0 && maker.two() == 0 ? 0 : 1;
}
