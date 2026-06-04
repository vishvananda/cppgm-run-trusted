// VALIDATION: compile-fail
// PA20 audit regression: an executed declaration with a non-constant
// initializer invalidates the enclosing constexpr evaluation.

int runtime_value();

constexpr int skipped_declaration()
{
  int ignored = runtime_value();
  return 1;
}

static_assert(skipped_declaration() == 1, "");

int main()
{
  return 0;
}
