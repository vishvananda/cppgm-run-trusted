namespace std {
template <class A, class B>
struct pair {
	pair(A, B);
};

template <class A, class B>
pair<A, B> make_pair(A&& a, B&& b)
{
	return pair<A, B>(a, b);
}
}

struct Item {};

std::pair<int, Item> build_pair(int& value, Item item)
{
	return std::make_pair(value, item);
}
