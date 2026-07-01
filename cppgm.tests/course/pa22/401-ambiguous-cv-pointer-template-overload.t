// VALIDATION: compile-fail
// Regression: two function templates that instantiate to the same pointer
// parameter type still participate independently in overload resolution.

template<typename T>
int pick(const T *)
{
  return 1;
}

template<typename T>
int pick(volatile T *)
{
  return 2;
}

int main()
{
  const volatile int *value = 0;
  return pick(value);
}
