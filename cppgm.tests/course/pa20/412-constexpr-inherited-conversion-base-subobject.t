template<bool B>
struct sink {};

template<typename T, T v>
struct integral_constant {
  static constexpr T value = v;
  using value_type = T;
  constexpr operator value_type() const { return value; }
};

struct derived_true : integral_constant<bool, true> {};

constexpr bool value = derived_true{};
sink<derived_true{}> s;
static_assert(value, "inherited conversion should use constexpr base object");
