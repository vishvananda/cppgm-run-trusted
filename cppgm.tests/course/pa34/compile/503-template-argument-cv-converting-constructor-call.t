template<class T>
struct Box {
	Box() {}

	template<class U>
	Box(const Box<U>&) {}
};

struct A {};

void take(Box<const A>) {}

void f() {
	Box<A> value;
	take(value);
}
