struct Guard {
  ~Guard();
};

bool cond();
void may_throw();

int main() {
  Guard outer;
  if (cond()) {
    Guard inner;
    may_throw();
  }
  may_throw();
  return 0;
}
