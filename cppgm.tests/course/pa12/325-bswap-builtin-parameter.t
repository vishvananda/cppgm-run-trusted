int f(unsigned x) {
	return __builtin_bswap32(x);
}

int main() {
	return f(1u);
}
