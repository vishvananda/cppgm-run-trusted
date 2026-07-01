struct Watch
{
	int value;
	Watch(int v) : value(v) {}
	Watch(const Watch& other) : value(other.value) {}
	Watch(Watch&& other) : value(other.value) { other.value = 0; }
	int get() const { return value; }
};

struct Pair
{
	Watch first;
	Watch second;
	Pair(int a, int b) : first(a), second(b) {}
	int sum() const { return first.get() + second.get(); }
};

struct Holder
{
	int value;

	template <class F>
	Holder(F f) : value(f()) {}

	int get() const { return value; }
};

int main()
{
	Pair p(3, 4);
	Holder h = [p]() { return p.sum(); };
	if (p.sum() != 7)
		return 1;
	return h.get() == 7 ? 0 : 2;
}
