struct Guard {
  ~Guard();
};

bool cond();
void may_throw();
int sink;

int main() {
  if (cond()) {
    Guard g;
    may_throw();
  }
  try {
    may_throw();
  } catch (...) {
    sink = 1;
  }
  return sink;
}
