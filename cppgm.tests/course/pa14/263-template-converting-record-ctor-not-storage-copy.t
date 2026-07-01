template<class T>
struct IterCompIter {
	T value;
};

template<class T>
struct IterCompVal {
	T value;

	explicit IterCompVal(IterCompIter<T>&& other)
		: value(other.value + 5)
	{
	}
};

template<class T>
int adjust_like(IterCompIter<T> comp)
{
	IterCompVal<T> converted(static_cast<IterCompIter<T>&&>(comp));
	return converted.value;
}

int main()
{
	IterCompIter<int> comp;
	comp.value = 37;
	return adjust_like(comp) == 42 ? 0 : 1;
}
