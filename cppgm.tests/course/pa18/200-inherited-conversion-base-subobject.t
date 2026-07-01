struct Empty
{
};

struct A
{
  int marker;

  A()
    : marker(7)
  {
  }
};

struct B
{
  int marker;

  B()
    : marker(11)
  {
  }
};

template<class T, class Base>
struct Convertible : Base
{
  T value;

  Convertible()
    : Base(),
      value()
  {
  }

  operator const T &() const
  {
    return value;
  }
};

typedef Convertible<A, Empty> ConvertsToA;
typedef Convertible<B, ConvertsToA> Source;

int use_a(const A & value)
{
  return value.marker;
}

int use_b(const B & value)
{
  return value.marker;
}

int main()
{
  Source value;
  return use_a(value) == 7 && use_b(value) == 11 ? 0 : 1;
}
