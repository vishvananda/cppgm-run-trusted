template<bool B>
struct flag {
	static constexpr bool value = B;
};

template<bool B>
constexpr bool flag<B>::value;

template<bool B>
int read_value()
{
	return flag<B>::value ? 3 : 5;
}

template<bool B>
int read_address()
{
	const bool* p = &flag<B>::value;
	return *p ? 7 : 11;
}

int main()
{
	if (read_value<true>() != 3)
		return 1;
	if (read_value<false>() != 5)
		return 2;
	if (read_address<true>() != 7)
		return 3;
	return 0;
}
