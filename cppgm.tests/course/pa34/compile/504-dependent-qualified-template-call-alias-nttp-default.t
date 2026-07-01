template<bool B, class T = int>
struct enable_if {};

template<class T>
struct enable_if<true, T> {
	typedef T type;
};

template<bool B, class T = int>
using enable_if_t = typename enable_if<B, T>::type;

template<class T1, class T2>
struct construction_check {
	template<class U1, class U2>
	static constexpr bool viable() {
		return true;
	}
};

template<class T1, class T2>
struct pair_like {
	template<class Check = construction_check<T1, T2>,
	         enable_if_t<Check::template viable<T1 const &, T2 const &>(),
	                     int> = 0>
	pair_like(T1 const &, T2 const &) {}
};

void f(int *ptr) {
	pair_like<int *, int *> value(ptr, ptr);
	(void)value;
}
