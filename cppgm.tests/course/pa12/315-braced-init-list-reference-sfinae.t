struct Probe {
  static int helper(int&);
  static char helper(...);

  typedef decltype(helper({})) type;
};
