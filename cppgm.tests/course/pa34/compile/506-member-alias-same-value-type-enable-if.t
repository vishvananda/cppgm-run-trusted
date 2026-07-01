template<bool B, class T = void>
struct enable_if {};

template<class T>
struct enable_if<true, T> {
	typedef T type;
};

template<class A, class B>
struct is_same {
	static const bool value = false;
};

template<class A>
struct is_same<A, A> {
	static const bool value = true;
};

template<class It>
struct iterator_traits {
	typedef typename It::value_type value_type;
};

struct int_iter {
	typedef int value_type;
};

template<class T>
struct tree {
	typedef T value_type;

	template<class It>
	using __same_value_type =
		is_same<value_type, typename iterator_traits<It>::value_type>;

	template<class It>
	typename enable_if<__same_value_type<It>::value>::type
	insert(It, It) {}

	template<class It>
	typename enable_if<!__same_value_type<It>::value>::type
	insert(It, It);
};

int main()
{
	tree<int> t;
	int_iter it;
	t.insert(it, it);
	return 0;
}
