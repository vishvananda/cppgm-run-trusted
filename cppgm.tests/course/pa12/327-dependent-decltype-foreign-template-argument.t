namespace std {
	template<typename T>
	struct identity {
		typedef T type;
	};

	template<typename T>
	typename identity<T>::type&& declval();

	struct failure_type {
	};

	template<typename T, typename Tag>
	struct result_success {
		typedef Tag invoke_type;
	};

	struct invoke_memfun_ref {
	};

	struct result_of_memfun_ref_impl {
		template<typename Fp, typename Tp1, typename... Args>
		static result_success<
			decltype((std::declval<Tp1>().*std::declval<Fp>())
			         (std::declval<Args>()...)),
			invoke_memfun_ref> test(int);

		template<typename...>
		static failure_type test(...);
	};
}

int main() {
	return 0;
}
