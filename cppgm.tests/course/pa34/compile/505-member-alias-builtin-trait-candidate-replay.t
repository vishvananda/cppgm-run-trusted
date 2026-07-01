template<bool B, class T = void>
struct enable_if {};

template<class T>
struct enable_if<true, T> {
	typedef T type;
};

template<class T>
struct base {
	base& operator=(const base&) { return *this; }
	template<class U>
	base& operator=(base<U>&&) { return *this; }
};

template<class T>
struct wrap : base<T> {
	typedef base<T> base_type;

	template<class U>
	using assignable =
		typename enable_if<__is_assignable(base_type&, wrap<U>),
		                   wrap&>::type;

	template<class U>
	assignable<U> operator=(wrap<U>&&) { return *this; }
};

struct X {};

int main()
{
	wrap<const X> lhs;
	wrap<X> rhs;
	lhs.operator=<X>(static_cast<wrap<X>&&>(rhs));
	return 0;
}
