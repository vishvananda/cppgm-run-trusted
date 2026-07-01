namespace std {
struct error_code {
private:
	template<typename T>
	error_code(T);
};

bool operator==(const error_code&, const error_code&);
}

using namespace std;

enum class TypeKind {
	Record,
	Pointer
};

bool f(TypeKind kind) {
	return kind == TypeKind::Record;
}

int main() {
	return f(TypeKind::Record) ? 0 : 1;
}
