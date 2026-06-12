struct KeyOrder {
  explicit KeyOrder(int v) : value(v) {}
  virtual int first();
  virtual int second();
  int value;
};

extern "C" int host_use_key_order(KeyOrder*);

