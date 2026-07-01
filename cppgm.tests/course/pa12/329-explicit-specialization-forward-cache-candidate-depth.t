namespace std {
struct streampos {};

template<typename>
struct char_traits;

template<>
struct char_traits<char>;
}

std::char_traits<char>* cached;

namespace std {
template<typename T>
struct char_traits {
  typedef int pos_type;
};

template<>
struct char_traits<char> {
  typedef streampos pos_type;
};
}

template<typename T, typename U = typename std::char_traits<char>::pos_type>
int f(T)
{
  return 0;
}

int main()
{
  return f(0);
}
