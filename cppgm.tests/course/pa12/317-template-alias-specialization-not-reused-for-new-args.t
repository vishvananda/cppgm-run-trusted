namespace std {
template<class T>
struct remove_reference {
  typedef T type;
};

template<class T>
struct remove_reference<T&> {
  typedef T type;
};

template<class T>
typename remove_reference<T>::type&& move(T&& value);
}

int&& get_int();
long&& get_long();

typedef decltype(std::move(get_int())) A;
typedef decltype(std::move(get_long())) B;
