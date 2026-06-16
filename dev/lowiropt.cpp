// Student-facing scaffold for the PA37 `lowiropt` binary.

#include "exceptions.h"
#include "lowiropt.h"
#include "tool_help_text.h"

#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace {

struct LowIROptInvocation
{
  bool has_optimization_level = false;
  int optimization_level = 0;
  string outfile;
  vector<string> inputs;
};

LowIROptInvocation parse_lowiropt_invocation(const vector<string> & args);

vector<string> collect_args(int argc, char ** argv)
{
  vector<string> args;
  for(int i = 1; i < argc; ++i) {
    args.push_back(argv[i]);
  }
  return args;
}

bool has_help_arg(const vector<string> & args)
{
  for(size_t i = 0; i < args.size(); ++i) {
    if(args[i] == "--help" || args[i] == "-h") {
      return true;
    }
  }
  return false;
}

bool has_batch_stdin_arg(const vector<string> & args)
{
  for(size_t i = 0; i < args.size(); ++i) {
    if(args[i] == "--batch-stdin") {
      return true;
    }
  }
  return false;
}

int run_batch_mode(const vector<string> & base_args)
{
  vector<string> inherited_args;
  for(size_t i = 0; i < base_args.size(); ++i) {
    if(base_args[i] != "--batch-stdin") {
      inherited_args.push_back(base_args[i]);
    }
  }

  string line;
  while(getline(cin, line)) {
    try {
      vector<string> fields;
      string field;
      for(size_t i = 0; i <= line.size(); ++i) {
        if(i == line.size() || line[i] == '\t') {
          fields.push_back(field);
          field.clear();
        }
        else {
          field.push_back(line[i]);
        }
      }
      if(fields.size() < 5) {
        cout << "EXIT_FAILURE" << endl;
        continue;
      }
      vector<string> args = inherited_args;
      args.insert(args.end(), fields.begin() + 4, fields.end());
      const LowIROptInvocation invocation = parse_lowiropt_invocation(args);
      lowiropt::Options options;
      options.optimization_level = invocation.optimization_level;
      options.outfile = fields[0];
      lowiropt::optimize_files_to_file(invocation.inputs, options);
      cout << "EXIT_SUCCESS" << endl;
    }
    catch(const NotImplementedException &) {
      cout << "EXIT_NOT_IMPLEMENTED" << endl;
    }
    catch(const exception &) {
      cout << "EXIT_FAILURE" << endl;
    }
  }
  return EXIT_SUCCESS;
}

bool is_optimization_level(const string & arg, int & level)
{
  if(arg == "-O0") {
    level = 0;
    return true;
  }
  if(arg == "-O1") {
    level = 1;
    return true;
  }
  if(arg == "-O2") {
    level = 2;
    return true;
  }
  return false;
}

bool starts_with_dash(const string & arg)
{
  return !arg.empty() && arg[0] == '-';
}

LowIROptInvocation parse_lowiropt_invocation(const vector<string> & args)
{
  LowIROptInvocation invocation;

  for(size_t i = 0; i < args.size(); ++i) {
    int optimization_level = 0;
    if(is_optimization_level(args[i], optimization_level)) {
      if(invocation.has_optimization_level) {
        throw logic_error("multiple optimization levels provided");
      }
      invocation.has_optimization_level = true;
      invocation.optimization_level = optimization_level;
      continue;
    }
    if(args[i] == "-o") {
      if(i + 1 >= args.size()) {
        throw logic_error("missing output file after -o");
      }
      if(!invocation.outfile.empty()) {
        throw logic_error("multiple output files provided");
      }
      invocation.outfile = args[++i];
      continue;
    }
    if(starts_with_dash(args[i])) {
      throw logic_error("unknown option: " + args[i]);
    }
    invocation.inputs.push_back(args[i]);
  }

  if(!invocation.has_optimization_level ||
     invocation.outfile.empty() ||
     invocation.inputs.empty()) {
    throw logic_error("invalid usage");
  }

  return invocation;
}

int run_lowiropt_mode(const vector<string> & args)
{
  if(has_batch_stdin_arg(args)) {
    return run_batch_mode(args);
  }

  if(has_help_arg(args)) {
    cout << lowiropt_help_text();
    return EXIT_SUCCESS;
  }

  const LowIROptInvocation invocation = parse_lowiropt_invocation(args);
  lowiropt::Options options;
  options.optimization_level = invocation.optimization_level;
  options.outfile = invocation.outfile;
  lowiropt::optimize_files_to_file(invocation.inputs, options);
  return EXIT_SUCCESS;
}

}  // namespace

int main(int argc, char ** argv)
{
  try
  {
    return run_lowiropt_mode(collect_args(argc, argv));
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
