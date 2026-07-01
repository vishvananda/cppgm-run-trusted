namespace std {
template<typename>
struct __is_integer {
  enum { __value = 0 };
};
}

namespace __gnu_cxx {
template<typename _Tp>
struct Helper : public std::__is_integer<_Tp> {
  using std::__is_integer<_Tp>::__value;
  enum { __width = __value ? sizeof(_Tp) * __CHAR_BIT__ : 0 };
};

template<typename _Value>
struct Traits {
  static const bool sign = (_Value)(-1) < 0;
  static const int digits = Helper<_Value>::__width - sign;
  static const _Value max = sign ? (((((_Value)1 << (digits - 1)) - 1) << 1) + 1) : ~(_Value)0;
  static const _Value min = sign ? -max - 1 : (_Value)0;
};

template<typename _Value>
const _Value Traits<_Value>::min;

template<typename _Value>
const _Value Traits<_Value>::max;

template<typename _Value>
const bool Traits<_Value>::sign;

template<typename _Value>
const int Traits<_Value>::digits;
}

int main()
{
  return 0;
}
