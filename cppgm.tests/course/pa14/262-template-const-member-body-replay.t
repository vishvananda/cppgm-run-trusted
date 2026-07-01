namespace mini {

template<class T>
struct less {
};

template<class T>
struct allocator {
};

template<class T>
struct _Identity {
};

template<class Key, class Val, class KeyOfValue, class Compare, class Alloc>
struct _Rb_tree {
	struct iterator {
	};

	struct const_iterator {
		const_iterator()
		{
		}

		const_iterator(iterator)
		{
		}
	};

	iterator find(const Key&)
	{
		return iterator();
	}

	const_iterator find(const Key&) const
	{
		return const_iterator();
	}

	iterator end()
	{
		return iterator();
	}

	const_iterator end() const
	{
		return const_iterator();
	}
};

template<class Key, class Compare = less<Key>, class Alloc = allocator<Key> >
struct set {
	typedef Key key_type;
	typedef _Rb_tree<key_type, key_type, _Identity<key_type>, Compare, Alloc> _Rep_type;
	typedef typename _Rep_type::iterator iterator;
	typedef typename _Rep_type::const_iterator const_iterator;

	_Rep_type _M_t;

	iterator find(const key_type& __x)
	{
		return _M_t.find(__x);
	}

	const_iterator find(const key_type& __x) const
	{
		return _M_t.find(__x);
	}

	iterator end()
	{
		return _M_t.end();
	}

	const_iterator end() const
	{
		return _M_t.end();
	}
};

}

namespace pa11 {
struct Binding {
};
}

using pa11::Binding;

bool a(const mini::set<Binding*>& deleted, Binding* ctor)
{
	deleted.find(ctor);
	deleted.end();
	return true;
}

bool b(mini::set<Binding*>& deleted, Binding* ctor)
{
	deleted.find(ctor);
	deleted.end();
	return true;
}

bool c(const mini::set<Binding*>& deleted, Binding* ctor)
{
	deleted.find(ctor);
	deleted.end();
	return true;
}

int main()
{
	mini::set<Binding*> set;
	Binding binding;
	bool x = a(set, &binding);
	bool y = b(set, &binding);
	bool z = c(set, &binding);
	return x && y && z ? 0 : 1;
}
