template <typename T>
T&& declval();

template <typename...>
using void_t = void;

template <typename T, typename = void>
struct has_hidden_query
{
  static constexpr bool value = false;
};

template <typename T>
struct has_hidden_query<T, void_t<decltype(query(declval<T>()))> >
{
  static constexpr bool value = true;
};

template <typename T>
struct tag
{
  friend int query(const tag&)
  {
    return 1;
  }
};

static_assert(has_hidden_query<tag<int> >::value, "hidden friend ADL");

int main()
{
  return has_hidden_query<tag<int> >::value ? 0 : 1;
}
