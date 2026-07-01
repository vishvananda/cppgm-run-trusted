struct Vec {
	Vec(int);
};

Vec::Vec(int value)
{
	(void)value;
}

bool accepts_value(const Vec& value)
{
	(void)value;
	return true;
}

bool test()
{
	return accepts_value({1});
}
