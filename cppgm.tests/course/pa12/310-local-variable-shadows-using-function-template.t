namespace N {
template<class T> T next(T, int);
template<class T> T count(T, T);
}

using namespace N;

int f() {
  int next = 0;
  next = 1;
  return next;
}

int g(int pos) {
  int count = 0;
  return count < 3 && pos < 5;
}
