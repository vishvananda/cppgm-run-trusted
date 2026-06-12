// Student-facing scaffold for the PA10+ `cppgm++` binary.

#include "exceptions.h"
#include "pa10_ast.h"
#include "pa11_types.h"
#include "pa12_semantics.h"
#include "pa14_lowir.h"
#include "pa29_toolchain.h"
#include "tool_help_text.h"

#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace {

enum class EmitMode
{
  None,
  Ast,
  Types,
  Semantics,
  LowIR,
};

enum class DriverMode
{
  Query,
  Preprocess,
  Compile,
  Link,
};

struct DriverInvocation
{
  DriverMode mode;
  string outfile;
  string target;
  int optimization_level;
  vector<string> include_paths;
  vector<string> library_paths;
  vector<string> libraries;
  vector<string> inputs;

  DriverInvocation()
      : mode(DriverMode::Link),
        optimization_level(0)
  {
  }
};

vector<string> collect_args(int argc, char ** argv)
{
  vector<string> args;
  for(int i = 1; i < argc; ++i) {
    args.push_back(argv[i]);
  }
  return args;
}

bool has_arg(const vector<string> & args, const string & needle)
{
  for(size_t i = 0; i < args.size(); ++i) {
    if(args[i] == needle) {
      return true;
    }
  }
  return false;
}

bool has_help_arg(const vector<string> & args)
{
  return has_arg(args, "--help") || has_arg(args, "-h");
}

bool starts_with(const string & value, const string & prefix)
{
  return value.size() >= prefix.size() &&
      value.compare(0, prefix.size(), prefix) == 0;
}

bool is_query_driver_flag(const string & arg)
{
  return arg == "--version" ||
      arg == "-v" ||
      arg == "-dumpmachine" ||
      arg == "-dumpversion" ||
      arg == "-print-search-dirs";
}

bool is_optimization_flag(const string & arg)
{
  return starts_with(arg, "-O");
}

int optimization_level_for_flag(const string & arg)
{
  if(arg == "-O0") {
    return 0;
  }
  if(arg == "-O" || arg == "-O1" || arg == "-Og") {
    return 1;
  }
  if(arg == "-O2" || arg == "-Os" || arg == "-Oz") {
    return 2;
  }
  if(arg == "-O3" || arg == "-Ofast") {
    return 3;
  }
  return 1;
}

bool is_benign_driver_flag(const string & arg)
{
  return arg == "-Wall" ||
      arg == "-Winvalid-offsetof" ||
      arg == "-pipe" ||
      arg == "-w" ||
      arg == "-pg" ||
      arg == "-pedantic" ||
      arg == "-pedantic-errors" ||
      starts_with(arg, "-W") ||
      starts_with(arg, "-f") ||
      starts_with(arg, "-m") ||
      starts_with(arg, "-std=");
}

logic_error missing_option_argument(const string & option,
                                    const string & expected)
{
  return logic_error("missing " + expected + " after " + option);
}

void consume_required_option_argument(const vector<string> & args,
                                      size_t & i,
                                      const string & option,
                                      const string & expected)
{
  if(i + 1 >= args.size()) {
    throw missing_option_argument(option, expected);
  }
  ++i;
}

bool consume_joined_or_separate_option(const vector<string> & args,
                                       size_t & i,
                                       const string & option,
                                       const string & expected)
{
  if(args[i] == option) {
    consume_required_option_argument(args, i, option, expected);
    return true;
  }
  if(starts_with(args[i], option) && args[i].size() > option.size()) {
    return true;
  }
  return false;
}

bool take_joined_or_separate_option(const vector<string> & args,
                                    size_t & i,
                                    const string & option,
                                    const string & expected,
                                    string & out)
{
  if(args[i] == option) {
    consume_required_option_argument(args, i, option, expected);
    out = args[i];
    return true;
  }
  if(starts_with(args[i], option) && args[i].size() > option.size()) {
    out = args[i].substr(option.size());
    return true;
  }
  return false;
}

vector<string> split_tab_fields(const string & line)
{
  vector<string> fields;
  size_t pos = 0;
  while(pos <= line.size()) {
    const size_t next = line.find('\t', pos);
    if(next == string::npos) {
      fields.push_back(line.substr(pos));
      break;
    }
    fields.push_back(line.substr(pos, next - pos));
    pos = next + 1;
  }
  return fields;
}

void truncate_file(const string & path)
{
  ofstream out(path.c_str());
  if(!out) {
    throw runtime_error("cannot open output capture");
  }
}

void consume_emit_flag(vector<string> & args,
                       const string & flag,
                       EmitMode value,
                       EmitMode & out)
{
  vector<string> kept;
  bool found = false;
  for(size_t i = 0; i < args.size(); ++i) {
    if(args[i] == flag) {
      found = true;
      continue;
    }
    kept.push_back(args[i]);
  }

  if(!found) {
    return;
  }

  if(out != EmitMode::None) {
    throw logic_error("multiple --emit-* options provided");
  }
  out = value;
  args.swap(kept);
}

EmitMode parse_emit_mode(vector<string> & args)
{
  EmitMode mode = EmitMode::None;
  consume_emit_flag(args, "--emit-ast", EmitMode::Ast, mode);
  consume_emit_flag(args, "--emit-types", EmitMode::Types, mode);
  consume_emit_flag(args, "--emit-semantics", EmitMode::Semantics, mode);
  consume_emit_flag(args, "--emit-lowir", EmitMode::LowIR, mode);
  return mode;
}

void parse_source_output_invocation(const vector<string> & args,
                                    bool allow_lowir_options,
                                    string * outfile,
                                    vector<string> * inputs_out)
{
  bool explicit_outfile = false;
  vector<string> inputs;

  for(size_t i = 0; i < args.size(); ++i) {
    if(args[i] == "-o") {
      consume_required_option_argument(args, i, "-o", "output file");
      if(outfile != nullptr) {
        *outfile = args[i];
      }
      explicit_outfile = true;
      continue;
    }
    if(allow_lowir_options && is_optimization_flag(args[i])) {
      continue;
    }
    if(allow_lowir_options &&
       (args[i] == "--witness" || args[i] == "--witness-debug")) {
      consume_required_option_argument(args, i, args[i], "output file");
      continue;
    }
    if(args[i] == "-c" || args[i] == "-E" || is_query_driver_flag(args[i])) {
      throw logic_error("invalid usage");
    }
    if(starts_with(args[i], "-")) {
      throw logic_error("unsupported option in emit mode: " + args[i]);
    }
    inputs.push_back(args[i]);
  }

  if(!explicit_outfile || inputs.empty()) {
    throw logic_error("invalid usage");
  }
  if(inputs_out != nullptr) {
    *inputs_out = inputs;
  }
}

void parse_source_output_invocation(const vector<string> & args,
                                    bool allow_lowir_options)
{
  parse_source_output_invocation(args, allow_lowir_options, nullptr, nullptr);
}

preproc::Options make_preproc_options()
{
  time_t now = time(NULL);
  tm * local = localtime(&now);
  if(local == NULL) {
    throw runtime_error("cannot read build time");
  }
  char * text = asctime(local);
  if(text == NULL) {
    throw runtime_error("cannot format build time");
  }
  const string stamp(text);
  if(stamp.size() < 24) {
    throw runtime_error("invalid build time");
  }

  preproc::Options options;
  options.author = "Vishvananda Ishaya";
  options.build_date = stamp.substr(4, 6) + " " + stamp.substr(20, 4);
  options.build_time = stamp.substr(11, 8);
  options.include_paths.push_back("dev/include");
  options.include_paths.push_back("../dev/include");
  return options;
}

bool consume_preprocess_option(const vector<string> & args, size_t & i)
{
  if(consume_joined_or_separate_option(args, i, "-D", "macro definition")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-U", "macro name")) {
    return true;
  }
  if(args[i] == "-include") {
    consume_required_option_argument(args, i, "-include", "file");
    return true;
  }
  return false;
}

bool consume_search_option(const vector<string> & args, size_t & i)
{
  if(consume_joined_or_separate_option(args, i, "-I", "path")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-isystem", "path")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-L", "path")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-l", "library name")) {
    return true;
  }
  return false;
}

bool consume_dependency_option(const vector<string> & args, size_t & i)
{
  if(args[i] == "-MMD" || args[i] == "-MD" || args[i] == "-MP") {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-MF", "depfile path")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-MT", "target")) {
    return true;
  }
  if(consume_joined_or_separate_option(args, i, "-MQ", "target")) {
    return true;
  }
  return false;
}

bool consume_toolchain_option(const vector<string> & args, size_t & i)
{
  if(args[i] == "-g0" ||
     args[i] == "-gline-tables-only" ||
     args[i] == "-g" ||
     starts_with(args[i], "-g")) {
    return true;
  }
  if(is_optimization_flag(args[i])) {
    return true;
  }
  if(args[i] == "--target") {
    consume_required_option_argument(args, i, "--target", "target");
    return true;
  }
  if(starts_with(args[i], "--target=")) {
    if(args[i].size() == string("--target=").size()) {
      throw missing_option_argument("--target", "target");
    }
    return true;
  }
  if(args[i] == "-std") {
    consume_required_option_argument(args, i, "-std", "language standard");
    return true;
  }
  if(args[i] == "-stdlib") {
    consume_required_option_argument(args, i, "-stdlib", "standard library name");
    return true;
  }
  if(starts_with(args[i], "-stdlib=")) {
    return true;
  }
  if(args[i] == "-pthread") {
    throw logic_error("option not yet supported: -pthread");
  }
  return false;
}

DriverInvocation parse_driver_invocation(const vector<string> & args)
{
  if(args.empty()) {
    throw logic_error("invalid usage");
  }

  DriverInvocation invocation;
  if(is_query_driver_flag(args[0])) {
    if(args.size() != 1) {
      throw logic_error("query flag must be used as a direct invocation");
    }
    invocation.mode = DriverMode::Query;
    return invocation;
  }

  bool compile_only = false;
  bool preprocess_only = false;
  bool explicit_outfile = false;

  for(size_t i = 0; i < args.size(); ++i) {
    string value;
    if(is_query_driver_flag(args[i])) {
      throw logic_error("query flag must be used as a direct invocation");
    }
    if(args[i] == "-c") {
      compile_only = true;
      continue;
    }
    if(args[i] == "-E") {
      preprocess_only = true;
      continue;
    }
    if(is_optimization_flag(args[i])) {
      invocation.optimization_level = optimization_level_for_flag(args[i]);
      continue;
    }
    if(args[i] == "-o") {
      consume_required_option_argument(args, i, "-o", "output file");
      if(explicit_outfile) {
        throw logic_error("multiple output files provided");
      }
      invocation.outfile = args[i];
      explicit_outfile = true;
      continue;
    }
    if(take_joined_or_separate_option(args, i, "-I", "path", value) ||
       take_joined_or_separate_option(args, i, "-isystem", "path", value)) {
      invocation.include_paths.push_back(value);
      continue;
    }
    if(take_joined_or_separate_option(args, i, "-L", "path", value)) {
      invocation.library_paths.push_back(value);
      continue;
    }
    if(take_joined_or_separate_option(args, i, "-l", "library name", value)) {
      invocation.libraries.push_back(value);
      continue;
    }
    if(args[i] == "--target") {
      consume_required_option_argument(args, i, "--target", "target");
      if(!invocation.target.empty()) {
        throw logic_error("multiple --target options provided");
      }
      invocation.target = args[i];
      continue;
    }
    if(starts_with(args[i], "--target=")) {
      if(args[i].size() == string("--target=").size()) {
        throw missing_option_argument("--target", "target");
      }
      if(!invocation.target.empty()) {
        throw logic_error("multiple --target options provided");
      }
      invocation.target = args[i].substr(string("--target=").size());
      continue;
    }
    if(consume_preprocess_option(args, i) ||
       consume_dependency_option(args, i) ||
       consume_toolchain_option(args, i) ||
       is_benign_driver_flag(args[i])) {
      continue;
    }
    if(starts_with(args[i], "-")) {
      throw logic_error("unsupported driver option: " + args[i]);
    }
    invocation.inputs.push_back(args[i]);
  }

  if(compile_only && preprocess_only) {
    throw logic_error("cannot combine -c and -E");
  }
  if(invocation.inputs.empty()) {
    throw logic_error("invalid usage");
  }
  if(!explicit_outfile) {
    throw logic_error("missing output file");
  }
  if((compile_only || preprocess_only) && invocation.inputs.size() != 1) {
    throw logic_error("cannot specify -o when generating multiple output files");
  }

  invocation.mode =
      preprocess_only ? DriverMode::Preprocess :
      compile_only ? DriverMode::Compile :
      DriverMode::Link;
  return invocation;
}

int run_unimplemented_mode(const char * feature,
                           const char * owner)
{
  (void)feature;
  (void)owner;
  throw NotImplementedException();
}

pa29::Options make_pa29_options(const DriverInvocation & invocation)
{
  pa29::Options options;
  options.preprocess = make_preproc_options();
  vector<string> builtin_include_paths = options.preprocess.include_paths;
  options.preprocess.include_paths = invocation.include_paths;
  options.preprocess.include_paths.insert(options.preprocess.include_paths.end(),
                                          builtin_include_paths.begin(),
                                          builtin_include_paths.end());
  options.target = invocation.target;
  options.optimization_level = invocation.optimization_level;
  options.library_paths = invocation.library_paths;
  options.libraries = invocation.libraries;
  return options;
}

int run_emit_ast_mode(const vector<string> & args)
{
  string outfile;
  vector<string> srcfiles;
  parse_source_output_invocation(args, false, &outfile, &srcfiles);
  pa10::Options options;
  options.preprocess = make_preproc_options();
  pa10::emit_ast(srcfiles, outfile, options);
  return EXIT_SUCCESS;
}

int run_emit_types_mode(const vector<string> & args)
{
  string outfile;
  vector<string> srcfiles;
  parse_source_output_invocation(args, false, &outfile, &srcfiles);
  pa11::Options options;
  options.preprocess = make_preproc_options();
  pa11::emit_types(srcfiles, outfile, options);
  return EXIT_SUCCESS;
}

int run_emit_semantics_mode(const vector<string> & args)
{
  string outfile;
  vector<string> srcfiles;
  parse_source_output_invocation(args, false, &outfile, &srcfiles);
  pa12::Options options;
  options.preprocess = make_preproc_options();
  pa12::emit_semantics(srcfiles, outfile, options);
  return EXIT_SUCCESS;
}

int run_emit_lowir_mode(const vector<string> & args)
{
  string outfile;
  vector<string> srcfiles;
  parse_source_output_invocation(args, true, &outfile, &srcfiles);
  pa14::Options options;
  options.preprocess = make_preproc_options();
  pa14::emit_lowir(srcfiles, outfile, options);
  return EXIT_SUCCESS;
}

int run_driver_mode(const vector<string> & args)
{
  const DriverInvocation invocation = parse_driver_invocation(args);
  switch(invocation.mode) {
  case DriverMode::Query:
    return run_unimplemented_mode("driver query mode", "PA34");
  case DriverMode::Preprocess:
    return run_unimplemented_mode("hosted preprocess driver mode (-E)", "PA34");
  case DriverMode::Compile:
    pa29::compile_source_to_object(invocation.inputs[0],
                                   invocation.outfile,
                                   make_pa29_options(invocation));
    return EXIT_SUCCESS;
  case DriverMode::Link:
    pa29::link_inputs_to_executable(invocation.inputs,
                                    invocation.outfile,
                                    make_pa29_options(invocation));
    return EXIT_SUCCESS;
  }
  throw logic_error("unreachable driver mode");
}

int run_cppgm(const vector<string> & raw_args);

const char * batch_status_name(int status)
{
  if(status == EXIT_SUCCESS) {
    return "EXIT_SUCCESS";
  }
  if(status == CPPGM_EXIT_NOT_IMPLEMENTED) {
    return "EXIT_NOT_IMPLEMENTED";
  }
  return "EXIT_FAILURE";
}

int run_one_batch_request(const vector<string> & fields)
{
  if(fields.size() < 5) {
    return EXIT_FAILURE;
  }
  truncate_file(fields[0]);
  if(fields[1] != fields[0]) {
    truncate_file(fields[1]);
  }

  ofstream out(fields[0].c_str(), ios::app);
  ofstream err(fields[1].c_str(), ios::app);
  if(!out || !err) {
    return EXIT_FAILURE;
  }
  streambuf * old_cout = cout.rdbuf(out.rdbuf());
  streambuf * old_cerr = cerr.rdbuf(err.rdbuf());
  int status = EXIT_FAILURE;
  try {
    vector<string> args(fields.begin() + 4, fields.end());
    status = run_cppgm(args);
  }
  catch(const NotImplementedException & e) {
    cerr << "ERROR: " << e.what() << endl;
    status = CPPGM_EXIT_NOT_IMPLEMENTED;
  }
  catch(const exception & e) {
    cerr << "ERROR: " << e.what() << endl;
    status = EXIT_FAILURE;
  }
  cout.rdbuf(old_cout);
  cerr.rdbuf(old_cerr);
  return status;
}

int run_batch_mode()
{
  string line;
  while(getline(cin, line)) {
    const int status = run_one_batch_request(split_tab_fields(line));
    cout << batch_status_name(status) << endl;
  }
  return EXIT_SUCCESS;
}

int run_cppgm(const vector<string> & raw_args)
{
  if(has_arg(raw_args, "--batch-stdin")) {
    return run_batch_mode();
  }

  if(has_help_arg(raw_args)) {
    cout << cppgm_help_text();
    return EXIT_SUCCESS;
  }

  vector<string> args = raw_args;
  const EmitMode mode = parse_emit_mode(args);

  switch(mode) {
  case EmitMode::Ast:
    return run_emit_ast_mode(args);
  case EmitMode::Types:
    return run_emit_types_mode(args);
  case EmitMode::Semantics:
    return run_emit_semantics_mode(args);
  case EmitMode::LowIR:
    return run_emit_lowir_mode(args);
  case EmitMode::None:
    return run_driver_mode(args);
  }

  throw logic_error("unreachable emit mode");
}

}  // namespace

int main(int argc, char ** argv)
{
  try
  {
    return run_cppgm(collect_args(argc, argv));
  }
  catch(const NotImplementedException & e)
  {
    cerr << "ERROR: " << e.what() << endl;
    return CPPGM_EXIT_NOT_IMPLEMENTED;
  }
  catch(const exception & e)
  {
    cerr << "ERROR: " << e.what() << endl;
    return EXIT_FAILURE;
  }
}
