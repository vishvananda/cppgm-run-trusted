#include "200-host-key-function-order-import.helper.h"

int KeyOrder::first()
{
  return value + 9;
}

extern "C" int host_use_key_order(KeyOrder* object)
{
  return object->first() + object->second();
}

