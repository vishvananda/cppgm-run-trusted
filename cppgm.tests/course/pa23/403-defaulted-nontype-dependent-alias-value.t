template<bool B>
struct integral_constant
{
  static const bool value = B;
};

typedef integral_constant<true> true_type;
typedef integral_constant<false> false_type;

template<bool, class T = void>
struct enable_if
{
};

template<class T>
struct enable_if<true, T>
{
  typedef T type;
};

template<bool B>
using BoolConstant = integral_constant<B>;

template<class T>
using enable_if_t = typename enable_if<T::value>::type;

template<class...>
using expand_to_true = true_type;

template<class... P>
expand_to_true<enable_if_t<P>...> and_helper(int);

template<class...>
false_type and_helper(...);

template<class... P>
using And = decltype(and_helper<P...>(0));

template<class... T>
struct tuple
{
  template<class... U>
  struct IsThisTuple : false_type
  {
  };

  template<class A>
  struct Not : BoolConstant<!A::value>
  {
  };

  template<class A, class B>
  struct is_constructible : true_type
  {
  };

  template<class... U>
  struct Enable
      : And<BoolConstant<sizeof...(T) >= 1>,
            Not<IsThisTuple<U...> >,
            is_constructible<T, U>...>
  {
  };

  template<class... U,
           typename enable_if<
               And<BoolConstant<sizeof...(U) == sizeof...(T)>,
                   Enable<U...> >::value,
               int>::type = 0>
  tuple(U&&...)
  {
  }
};

int main()
{
  tuple<int> t(0);
  return 0;
}
