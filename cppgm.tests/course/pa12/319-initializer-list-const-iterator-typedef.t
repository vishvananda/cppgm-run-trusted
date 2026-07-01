#include <initializer_list>

void use(std::initializer_list<int> values)
{
	typedef std::initializer_list<int>::const_iterator Iter;
	Iter it = values.begin();
	(void)it;
}
