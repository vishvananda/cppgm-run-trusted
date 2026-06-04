// VALIDATION: compile-fail
// PA20 audit regression: a member call on a temporary must not fabricate a
// constant object when the temporary's constructor argument is not constant.

int runtime_value();

struct Box
{
  int value;

  constexpr explicit Box(int v) : value(v) {}
  constexpr int always() const { return 7; }
};

static_assert(Box(runtime_value()).always() == 7, "");

int main()
{
  return 0;
}
