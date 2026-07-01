void release(void* p)
{
	__builtin_operator_delete(p);
}

int main()
{
	return 0;
}
