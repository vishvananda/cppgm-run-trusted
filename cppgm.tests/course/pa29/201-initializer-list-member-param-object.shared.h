#pragma once

namespace std {
template<class E>
class initializer_list {
	const E* __b;
	decltype(sizeof(0)) __n;
	constexpr initializer_list(const E* b, decltype(sizeof(0)) n)
		: __b(b), __n(n) {}

public:
	constexpr initializer_list() : __b(0), __n(0) {}
	const E* begin() const { return __b; }
	const E* end() const { return __b + __n; }
	decltype(sizeof(0)) size() const { return __n; }
};
}

struct CourseInitializerListMember {
	int total(std::initializer_list<int> values);
};
