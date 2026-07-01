# hosted vector by-value argument deep-copies before callee reallocation
#include <set>
#include <string>
#include <vector>

struct Tok {
  int kind;
  std::string text;
  std::set<std::string> unavailable;
  bool active_paste;
  std::string source_file;
  int source_line;
  int source_column;

  Tok() : kind(0), active_paste(false), source_line(0), source_column(0) {
  }

  Tok(int k, const std::string& s)
      : kind(k), text(s), active_paste(false), source_line(0),
        source_column(0) {
  }
};

std::vector<Tok> process(std::vector<Tok> tokens) {
  std::vector<Tok> replacement;
  for (int i = 0; i < 12; ++i) {
    Tok r(1, "replacement");
    r.unavailable.insert("R");
    replacement.push_back(r);
  }
  tokens.erase(tokens.begin(), tokens.begin() + 1);
  tokens.insert(tokens.begin(), replacement.begin(), replacement.end());
  return tokens;
}

std::vector<Tok> instantiate(const Tok& token) {
  std::vector<Tok> substituted;
  for (int i = 0; i < 4; ++i) {
    Tok copy = token;
    copy.text += "x";
    substituted.push_back(copy);
  }
  return process(substituted);
}

int main() {
  Tok t(1, "abc");
  t.unavailable.insert("x");
  std::vector<Tok> out = instantiate(t);
  if (out.size() != 15) {
    return 1;
  }
  if (out[0].text != "replacement") {
    return 2;
  }
  if (out[14].text != "abcx") {
    return 3;
  }
  return 0;
}
