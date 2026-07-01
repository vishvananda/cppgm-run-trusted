template<typename T>
struct Identity {
	typedef T type;
};

template<typename T>
struct Holder {
	typedef typename Identity<decltype((T()))>::type type;
};

int main() {
	Holder<int>::type value = 0;
	return value;
}
