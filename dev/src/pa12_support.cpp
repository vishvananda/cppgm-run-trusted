#include "pa12_internal.h"

#include <fstream>
#include <ostream>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Node::Node()
	: category(ValueCategory::PRValue),
	  binding(NULL),
	  direct_call(NULL),
	  has_op(false),
	  op(KW_ALIGNAS),
	  has_constant_value(false),
	  constant_value(0),
	  dependent_value_negated(false),
	  suppress_virtual_dispatch(false),
	  virtual_dispatch(false),
	  is_typeid_expression(false),
	  is_dynamic_cast_expression(false)
{
}

Node::Node(const string& text)
	: line(text),
	  category(ValueCategory::PRValue),
	  binding(NULL),
	  direct_call(NULL),
	  has_op(false),
	  op(KW_ALIGNAS),
	  has_constant_value(false),
	  constant_value(0),
	  dependent_value_negated(false),
	  suppress_virtual_dispatch(false),
	  virtual_dispatch(false),
	  is_typeid_expression(false),
	  is_dynamic_cast_expression(false)
{
}

QualifiedName::QualifiedName()
	: qualifier(NULL), qualified(false), has_template_arguments(false)
{
}

TemplateArgument::TemplateArgument()
	: kind(TemplateArgumentKind::Type),
	  template_declaration(NULL),
	  value_binding(NULL),
	  value(0),
	  dependent(false),
	  value_negated(false),
	  pack_expansion(false),
	  value_expr_begin(0),
	  value_expr_end(0)
{
}

TemplateArgument TemplateArgument::type_arg(TypePtr type)
{
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Type;
	arg.type = type;
	return arg;
}

TemplateArgument TemplateArgument::value_arg(TypePtr type, uint64_t value)
{
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Value;
	arg.type = type;
	arg.value = value;
	return arg;
}

TemplateArgument TemplateArgument::dependent_value_arg(TypePtr type)
{
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Value;
	arg.type = type;
	arg.dependent = true;
	return arg;
}

TemplateArgument TemplateArgument::template_arg(TemplateDeclaration* declaration)
{
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Template;
	arg.template_declaration = declaration;
	return arg;
}

TemplateArgument TemplateArgument::pack_arg(const vector<TemplateArgument>& values)
{
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Pack;
	arg.pack = values;
	return arg;
}

Expr::Expr()
	: category(ValueCategory::PRValue),
	  binding(NULL),
	  pack_expansion(false),
	  valid(false),
	  null_pointer_constant(false),
	  constant_expression(false),
	  has_constant_value(false),
	  constant_value(0),
	  builtin_constant_p(false),
	  braced_init_list(false),
		  copy_initialization(false),
		  dependent_value_negated(false),
		  source_begin(0),
		  source_end(0)
	{
	}

DeclSpecs::DeclSpecs()
	: typedef_decl(false),
	  constexpr_decl(false),
	  static_decl(false),
	  mutable_decl(false),
	  friend_decl(false),
	  extern_decl(false),
	  thread_local_decl(false),
	  auto_decl(false),
	  virtual_decl(false),
	  inline_decl(false),
	  cv(pa11::CV_NONE)
{
}

PtrOp::PtrOp(PtrKind k, unsigned flags)
	: kind(k), cv(flags)
{
}

PtrOp::PtrOp(TypePtr class_type, unsigned flags)
	: kind(PtrKind::MemberPointer), cv(flags), member_class(class_type)
{
}

ParameterInfo::ParameterInfo()
	: is_pack_expansion(false),
	  has_default(false)
{
}

Suffix::Suffix(SuffixKind k)
	: kind(k),
	  unknown_bound(false),
	  bound(0),
	  array_bound_name(),
	  variadic(false),
	  function_cv(pa11::CV_NONE),
	  ref_qualifier(0),
	  noexcept_decl(false),
	  override_decl(false),
	  final_decl(false),
	  trailing_return()
{
}

Declarator::Declarator() : has_name(false)
{
}

PendingFunctionBody::PendingFunctionBody()
	: function(NULL), body_pos(0), constructor_body(false), prebuilt_node(false)
{
}

TemplateParameterInfo::TemplateParameterInfo()
	: kind(TemplateParameterKind::Type),
	  is_pack(false),
	  has_default(false),
	  default_begin(0),
	  default_end(0)
{
}

TemplateDeclaration::TemplateDeclaration()
	: kind(TemplateDeclarationKind::Unknown),
	  owner(NULL),
	  lexical_scope(NULL),
	decl_begin(0),
	decl_end(0),
		has_definition(false),
		  constructor_template(false),
		  class_template_member(false),
		  class_specialization(false),
		  hidden_friend(false),
		  function_definition_validated(false),
		  friend_class_scope(NULL),
		placeholder(NULL),
		inherited_constructor_base(NULL),
		inherited_constructor_base_type()
{
}

ActiveClassInstantiation::ActiveClassInstantiation()
	: declaration(NULL)
{
}

ActiveClassInstantiation::ActiveClassInstantiation(TemplateDeclaration* d,
                                                   const string& n,
                                                   TypePtr t)
	: declaration(d), specialization_name(n), type(t)
{
}

Conversion::Conversion() : viable(false), rank(1000000)
{
}

Conversion::Conversion(bool ok, int cost, const Expr& converted)
	: viable(ok), rank(cost), expr(converted)
{
}

ConstexprValue::ConstexprValue()
	: valid(false),
	  is_float(false),
	  is_object(false),
	  is_pointer(false),
	  int_value(0),
	  float_value(0),
	  pointer_binding(NULL),
	  pointer_index(0)
{
}

ConstexprValue ConstexprValue::integer(uint64_t value)
{
	ConstexprValue out;
	out.valid = true;
	out.int_value = value;
	out.float_value = static_cast<long double>(value);
	return out;
}

ConstexprValue ConstexprValue::floating(long double value)
{
	ConstexprValue out;
	out.valid = true;
	out.is_float = true;
	out.float_value = value;
	out.int_value = static_cast<uint64_t>(value);
	return out;
}

ConstexprValue ConstexprValue::object(TypePtr type)
{
	ConstexprValue out;
	out.valid = true;
	out.is_object = true;
	out.object_type = type;
	return out;
}

ConstexprValue ConstexprValue::pointer(Binding* binding, long long index)
{
	ConstexprValue out;
	out.valid = true;
	out.is_pointer = true;
	out.pointer_binding = binding;
	out.pointer_index = index;
	return out;
}

void add_child(Node& parent, const Node& child)
{
	parent.children.push_back(child);
}

void annotate_expr_node(Expr& expr)
{
	expr.node.type = expr.type;
	expr.node.category = expr.category;
	expr.node.binding = expr.binding;
	expr.node.overloads = expr.overloads;
	expr.node.explicit_template_arguments = expr.explicit_template_arguments;
	expr.node.has_constant_value = expr.has_constant_value;
	expr.node.constant_value = expr.constant_value;
	expr.node.dependent_value_name = expr.dependent_value_name;
	expr.node.dependent_value_owner_template_name =
		expr.dependent_value_owner_template_name;
	expr.node.dependent_value_member_name = expr.dependent_value_member_name;
	expr.node.dependent_value_negated = expr.dependent_value_negated;
	expr.node.dependent_value_owner_template_arguments =
		expr.dependent_value_owner_template_arguments;
}

void dump_node(ostream& out, const Node& node, int depth)
{
	for (int i = 0; i < depth; ++i)
		out << "  ";
	out << node.line << '\n';
	for (size_t i = 0; i < node.children.size(); ++i)
		dump_node(out, node.children[i], depth + 1);
}

Parser::Parser(const string& srcfile, const Options& options)
	: pos_(0),
	  explicit_conversion_context_(0),
	  root_("translation-unit"),
	  local_type_counter_(0),
	  range_for_counter_(0),
	  force_new_function_binding_(false),
	  defer_function_template_bodies_(false),
	  suppress_implicit_template_base_init_(false),
	  parsing_base_specifier_(false),
	  validating_template_definition_(false),
	  override_function_parameter_names_(false),
	  replaying_dependent_decltype_(false),
	  parsing_default_template_argument_(false),
	  single_linkage_specification_declaration_(false),
		  defer_class_template_completion_depth_(0),
	  function_template_candidate_instantiation_depth_(0),
	  template_argument_expression_depth_(0),
	  unevaluated_expression_depth_(0),
	  suppress_qualifier_template_member_instantiation_depth_(0),
	  short_circuit_static_member_demand_depth_(0)
		{
		pa10::Options pa10_options;
		pa10_options.preprocess = options.preprocess;
		tokens_ = pa10::internal::collect_source_tokens(srcfile, pa10_options);
		declaration_tokens_ = tokens_;

		tu_.srcfile = srcfile;
	tu_.global_scope.reset(new Scope(ScopeKind::Namespace, "", NULL));
	scopes_.push_back(tu_.global_scope.get());
	pa11::add_binding(global_scope(),
	                  BindingKind::Type,
	                  "nullptr_t",
	                  pa11::make_fundamental(FT_NULLPTR_T));
	pa11::add_binding(global_scope(),
	                  BindingKind::Type,
	                  "__int128_t",
	                  pa11::make_fundamental(FT_INT128));
	pa11::add_binding(global_scope(),
	                  BindingKind::Type,
	                  "__uint128_t",
	                  pa11::make_fundamental(FT_UNSIGNED_INT128));
}

const Node& Parser::root() const
{
	return root_;
}

const vector<Node>& Parser::generated_nodes() const
{
	return generated_nodes_;
}

const vector<Node>& Parser::extra_lowir_nodes() const
{
	return extra_lowir_nodes_;
}

Scope* Parser::current_scope() const
{
	return scopes_.back();
}

Scope* Parser::global_scope() const
{
	return tu_.global_scope.get();
}

TypePtr Parser::current_return_type() const
{
	if (function_returns_.empty())
		return TypePtr();
	return function_returns_.back();
}

string Parser::current_language_linkage() const
{
	if (language_linkages_.empty())
		return "cpp";
	return language_linkages_.back();
}

bool Parser::at_eof() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::EndOfFile;
}

bool Parser::at_identifier() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Identifier;
}

bool Parser::at_literal() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Literal;
}

bool Parser::at(ETokenType type) const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       tokens_[pos_].type == type;
}

bool Parser::lookahead(ETokenType type, size_t offset) const
{
	size_t index = pos_ + offset;
	return index < tokens_.size() &&
	       tokens_[index].kind == posttoken::TokenKind::Simple &&
	       tokens_[index].type == type;
}

bool Parser::consume(ETokenType type)
{
	if (!at(type))
		return false;
	++pos_;
	return true;
}

void Parser::expect(ETokenType type)
{
	if (!consume(type))
		throw runtime_error("unexpected token: got '" +
		                    (pos_ < tokens_.size() ? tokens_[pos_].source :
		                     string("<eof>")) +
		                    "', expected " + to_string(type));
}

void Parser::expect_eof()
{
	if (!at_eof())
		throw runtime_error("expected end of file");
}

string Parser::consume_identifier()
{
	if (!at_identifier())
	{
		string prev = pos_ > 0 ? tokens_[pos_ - 1].source : string("<start>");
		string next = pos_ + 1 < tokens_.size()
			? tokens_[pos_ + 1].source : string("<eof>");
		throw runtime_error("expected identifier before '" + current().source +
		                    "' after '" + prev + "' next '" + next + "'");
	}
	return tokens_[pos_++].source;
}

string Parser::consume_literal()
{
	if (!at_literal())
		throw runtime_error("expected literal");
	return tokens_[pos_++].source;
}

const Token& Parser::current() const
{
	if (pos_ >= tokens_.size())
		throw runtime_error("token cursor out of range");
	return tokens_[pos_];
}

const Token& Parser::at_token(size_t index) const
{
	if (index >= tokens_.size())
		throw runtime_error("token index out of range");
	return tokens_[index];
}

void Parser::parse_translation_unit()
{
	while (!at_eof())
		parse_declaration_into(root_);
	expect_eof();
	for (size_t i = 0; i < template_declarations_.size(); ++i)
	{
		TemplateDeclaration* declaration = template_declarations_[i].get();
		if (declaration->kind != TemplateDeclarationKind::Class)
			continue;
		vector<TypePtr> specializations;
		for (map<string, TypePtr>::const_iterator it =
			     declaration->class_specializations.begin();
		     it != declaration->class_specializations.end();
		     ++it)
			specializations.push_back(it->second);
		for (size_t j = 0; j < specializations.size(); ++j)
		{
				TypePtr type = pa11::strip_cv(specializations[j]);
				if (candidate_only_class_template_specializations_.count(
					    type.get()) != 0)
					continue;
				if (demanded_class_template_specializations_.count(
					    type.get()) == 0)
					continue;
				map<const void*, vector<TemplateArgument> >::const_iterator args =
					record_template_arguments_.find(type.get());
			if (args == record_template_arguments_.end())
				continue;
			bool dependent = false;
			for (size_t k = 0; k < args->second.size(); ++k)
			{
				vector<TemplateArgument> pending;
				pending.push_back(args->second[k]);
				while (!pending.empty())
				{
					TemplateArgument arg = pending.back();
					pending.pop_back();
					if (arg.kind == TemplateArgumentKind::Type)
					{
						if (type_is_template_dependent(arg.type))
							dependent = true;
					}
					else if (arg.kind == TemplateArgumentKind::Value)
					{
						if (arg.dependent ||
						    type_is_template_dependent(arg.type))
							dependent = true;
					}
					else if (arg.kind == TemplateArgumentKind::Template)
					{
						if (arg.template_declaration == NULL)
							dependent = true;
					}
					else
					{
						for (size_t p = 0; p < arg.pack.size(); ++p)
							pending.push_back(arg.pack[p]);
					}
				}
			}
			if (dependent)
				continue;
			complete_template_record(type);
			instantiate_member_function_templates(type);
			instantiate_member_variable_templates(type);
		}
	}
}

void Parser::skip_balanced(ETokenType open, ETokenType close)
{
	expect(open);
	int depth = 1;
	while (depth > 0 && !at_eof())
	{
		if (consume(open))
			++depth;
		else if (consume(close))
			--depth;
		else
			++pos_;
	}
}

}  // namespace internal

void emit_semantics(const vector<string>& srcfiles,
                    const string& outfile,
                    const Options& options)
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");

	vector<unique_ptr<internal::Parser> > parsers;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		unique_ptr<internal::Parser> parser(new internal::Parser(srcfiles[i], options));
		parser->parse_translation_unit();
		parsers.push_back(std::move(parser));
	}

	out << parsers.size() << " translation units\n";
	for (size_t i = 0; i < parsers.size(); ++i)
	{
		out << "start translation unit " << (i + 1) << '\n';
		internal::dump_node(out, parsers[i]->root(), 0);
		const vector<internal::Node>& generated = parsers[i]->generated_nodes();
		for (size_t j = 0; j < generated.size(); ++j)
			internal::dump_node(out, generated[j], 1);
		out << "end translation unit\n";
	}
}

}  // namespace pa12
