enum class Choice
{
	Left,
	Right
};

Choice select(bool take_left, Choice current)
{
	current = take_left ? current : Choice::Right;
	return current;
}
