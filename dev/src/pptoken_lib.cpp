#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <istream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace std;

#include "IPPTokenStream.h"
#include "pptoken_lib.h"

namespace pptoken {
namespace {

struct SourceChar
{
  int cp;
  size_t index;
  int line;
  int column;
};

struct TextChar
{
  int cp;
  size_t source_index;
  int line;
  int column;
  bool synthetic;
};

struct LogicalChar
{
  int cp;
  size_t width;
};

enum class HeaderState
{
  AtLineStart,
  Normal,
  AfterHash,
  AfterInclude
};

string location_message(int line, int column, const string & message)
{
  ostringstream out;
  out << line << ":" << column << ":" << message;
  return out.str();
}

string general_message(const string & message)
{
  return " " + message;
}

bool is_continuation(unsigned char c)
{
  return (c & 0xC0) == 0x80;
}

void append_utf8(int cp, string & out)
{
  if(cp <= 0x7F) {
    out.push_back(static_cast<char>(cp));
  } else if(cp <= 0x7FF) {
    out.push_back(static_cast<char>(0xC0 | (cp >> 6)));
    out.push_back(static_cast<char>(0x80 | (cp & 0x3F)));
  } else if(cp <= 0xFFFF) {
    out.push_back(static_cast<char>(0xE0 | (cp >> 12)));
    out.push_back(static_cast<char>(0x80 | ((cp >> 6) & 0x3F)));
    out.push_back(static_cast<char>(0x80 | (cp & 0x3F)));
  } else {
    out.push_back(static_cast<char>(0xF0 | (cp >> 18)));
    out.push_back(static_cast<char>(0x80 | ((cp >> 12) & 0x3F)));
    out.push_back(static_cast<char>(0x80 | ((cp >> 6) & 0x3F)));
    out.push_back(static_cast<char>(0x80 | (cp & 0x3F)));
  }
}

void advance_location(int cp, int & line, int & column)
{
  if(cp == '\n') {
    ++line;
    column = 1;
  } else {
    ++column;
  }
}

int decode_utf8_at(const string & bytes, size_t i, size_t & width)
{
  const unsigned char c0 = static_cast<unsigned char>(bytes[i]);
  if(c0 <= 0x7F) {
    width = 1;
    return c0;
  }
  if(c0 >= 0xC2 && c0 <= 0xDF) {
    if(i + 1 < bytes.size() && is_continuation(bytes[i + 1])) {
      width = 2;
      return ((c0 & 0x1F) << 6) |
          (static_cast<unsigned char>(bytes[i + 1]) & 0x3F);
    }
    return -1;
  }
  if(c0 >= 0xE0 && c0 <= 0xEF) {
    if(i + 2 >= bytes.size() ||
       !is_continuation(bytes[i + 1]) ||
       !is_continuation(bytes[i + 2])) {
      return -1;
    }
    const unsigned char c1 = static_cast<unsigned char>(bytes[i + 1]);
    const unsigned char c2 = static_cast<unsigned char>(bytes[i + 2]);
    const int cp = ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if(cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF)) {
      return -1;
    }
    width = 3;
    return cp;
  }
  if(c0 >= 0xF0 && c0 <= 0xF4) {
    if(i + 3 >= bytes.size() ||
       !is_continuation(bytes[i + 1]) ||
       !is_continuation(bytes[i + 2]) ||
       !is_continuation(bytes[i + 3])) {
      return -1;
    }
    const unsigned char c1 = static_cast<unsigned char>(bytes[i + 1]);
    const unsigned char c2 = static_cast<unsigned char>(bytes[i + 2]);
    const unsigned char c3 = static_cast<unsigned char>(bytes[i + 3]);
    const int cp = ((c0 & 0x07) << 18) |
        ((c1 & 0x3F) << 12) |
        ((c2 & 0x3F) << 6) |
        (c3 & 0x3F);
    if(cp < 0x10000 || cp > 0x10FFFF) {
      return -1;
    }
    width = 4;
    return cp;
  }
  return -1;
}

vector<SourceChar> decode_source(const string & bytes)
{
  vector<SourceChar> out;
  out.reserve(bytes.size());
  int line = 1;
  int column = 1;
  size_t index = 0;
  for(size_t i = 0; i < bytes.size();) {
    size_t width = 0;
    const int cp = decode_utf8_at(bytes, i, width);
    if(cp < 0) {
      throw runtime_error(location_message(line, column, "Invalid utf-8 character"));
    }
    SourceChar ch;
    ch.cp = cp;
    ch.index = index++;
    ch.line = line;
    ch.column = column;
    out.push_back(ch);
    advance_location(cp, line, column);
    i += width;
  }
  if(!out.empty() && out[0].cp == 0xFEFF) {
    out.erase(out.begin());
    for(size_t i = 0; i < out.size(); ++i) {
      out[i].index = i;
    }
  }
  return out;
}

bool byte_starts_invalid_utf8(const string & bytes, size_t i)
{
  size_t width = 0;
  return decode_utf8_at(bytes, i, width) < 0;
}

void skip_quoted_bytes(const string & bytes, size_t & i, char quote)
{
  ++i;
  while(i < bytes.size()) {
    const unsigned char c = static_cast<unsigned char>(bytes[i]);
    if(c == '\\' && i + 1 < bytes.size()) {
      i += 2;
      continue;
    }
    ++i;
    if(c == static_cast<unsigned char>(quote)) {
      return;
    }
  }
}

string sanitize_invalid_comment_bytes(const string & bytes)
{
  string out = bytes;
  for(size_t i = 0; i < out.size();) {
    if(out[i] == '"' || out[i] == '\'') {
      skip_quoted_bytes(out, i, out[i]);
      continue;
    }
    if(out[i] == '/' && i + 1 < out.size() && out[i + 1] == '/') {
      i += 2;
      while(i < out.size() && out[i] != '\n') {
        if(static_cast<unsigned char>(out[i]) >= 0x80 &&
           byte_starts_invalid_utf8(out, i)) {
          out[i] = ' ';
        }
        ++i;
      }
      continue;
    }
    if(out[i] == '/' && i + 1 < out.size() && out[i + 1] == '*') {
      i += 2;
      while(i < out.size()) {
        if(out[i] == '*' && i + 1 < out.size() && out[i + 1] == '/') {
          i += 2;
          break;
        }
        if(static_cast<unsigned char>(out[i]) >= 0x80 &&
           byte_starts_invalid_utf8(out, i)) {
          out[i] = ' ';
        }
        ++i;
      }
      continue;
    }
    ++i;
  }
  return out;
}

int trigraph_replacement(int c)
{
  switch(c) {
    case '=': return '#';
    case '/': return '\\';
    case '\'': return '^';
    case '(': return '[';
    case ')': return ']';
    case '!': return '|';
    case '<': return '{';
    case '>': return '}';
    case '-': return '~';
    default: return -1;
  }
}

TextChar make_text_char(const SourceChar & source, int cp)
{
  TextChar ch;
  ch.cp = cp;
  ch.source_index = source.index;
  ch.line = source.line;
  ch.column = source.column;
  ch.synthetic = false;
  return ch;
}

vector<TextChar> apply_trigraphs_and_line_splices(const vector<SourceChar> & source)
{
  vector<TextChar> out;
  const size_t source_size = source.size();
  out.reserve(source_size);
  for(size_t i = 0; i < source_size;) {
    TextChar ch;
    if(i + 2 < source_size && source[i].cp == '?' && source[i + 1].cp == '?') {
      const int replacement = trigraph_replacement(source[i + 2].cp);
      if(replacement >= 0) {
        ch = make_text_char(source[i], replacement);
        i += 3;
      } else {
        ch = make_text_char(source[i], source[i].cp);
        ++i;
      }
    } else {
      ch = make_text_char(source[i], source[i].cp);
      ++i;
    }
    if(ch.cp == '\\') {
      size_t lookahead = i;
      TextChar next;
      bool have_next = false;
      if(lookahead < source_size) {
        if(lookahead + 2 < source_size && source[lookahead].cp == '?' &&
           source[lookahead + 1].cp == '?') {
          const int replacement = trigraph_replacement(source[lookahead + 2].cp);
          if(replacement >= 0) {
            next = make_text_char(source[lookahead], replacement);
            lookahead += 3;
            have_next = true;
          }
        }
        if(!have_next) {
          next = make_text_char(source[lookahead], source[lookahead].cp);
          ++lookahead;
          have_next = true;
        }
      }
      if(have_next && next.cp == '\n') {
        i = lookahead;
        continue;
      }
    }
    out.push_back(ch);
  }
  return out;
}

void append_final_newline(vector<TextChar> & text, const vector<SourceChar> & source)
{
  if(text.empty() || text.back().cp == '\n') {
    return;
  }
  TextChar ch;
  ch.cp = '\n';
  ch.source_index = source.size();
  ch.synthetic = true;
  ch.line = text.back().line;
  ch.column = text.back().column + 1;
  text.push_back(ch);
}

vector<TextChar> translated_text(const vector<SourceChar> & source)
{
  vector<TextChar> text = apply_trigraphs_and_line_splices(source);
  append_final_newline(text, source);
  return text;
}

bool in_range(int cp, int first, int last)
{
  return cp >= first && cp <= last;
}

bool is_annex_e2(int cp)
{
  return in_range(cp, 0x0300, 0x036F) ||
      in_range(cp, 0x1DC0, 0x1DFF) ||
      in_range(cp, 0x20D0, 0x20FF) ||
      in_range(cp, 0xFE20, 0xFE2F);
}

bool is_annex_e1(int cp)
{
  if(cp == 0xA8 || cp == 0xAA || cp == 0xAD || cp == 0xAF ||
     cp == 0xB7 || cp == 0x2054) {
    return true;
  }
  return in_range(cp, 0xB2, 0xB5) ||
      in_range(cp, 0xB7, 0xBA) ||
      in_range(cp, 0xBC, 0xBE) ||
      in_range(cp, 0xC0, 0xD6) ||
      in_range(cp, 0xD8, 0xF6) ||
      in_range(cp, 0xF8, 0xFF) ||
      in_range(cp, 0x0100, 0x167F) ||
      in_range(cp, 0x1681, 0x180D) ||
      in_range(cp, 0x180F, 0x1FFF) ||
      in_range(cp, 0x200B, 0x200D) ||
      in_range(cp, 0x202A, 0x202E) ||
      in_range(cp, 0x203F, 0x2040) ||
      in_range(cp, 0x2060, 0x206F) ||
      in_range(cp, 0x2070, 0x218F) ||
      in_range(cp, 0x2460, 0x24FF) ||
      in_range(cp, 0x2776, 0x2793) ||
      in_range(cp, 0x2C00, 0x2DFF) ||
      in_range(cp, 0x2E80, 0x2FFF) ||
      in_range(cp, 0x3004, 0x3007) ||
      in_range(cp, 0x3021, 0x302F) ||
      in_range(cp, 0x3031, 0x303F) ||
      in_range(cp, 0x3040, 0xD7FF) ||
      in_range(cp, 0xF900, 0xFD3D) ||
      in_range(cp, 0xFD40, 0xFDCF) ||
      in_range(cp, 0xFDF0, 0xFE44) ||
      in_range(cp, 0xFE47, 0xFFFD) ||
      in_range(cp, 0x10000, 0x1FFFD) ||
      in_range(cp, 0x20000, 0x2FFFD) ||
      in_range(cp, 0x30000, 0x3FFFD) ||
      in_range(cp, 0x40000, 0x4FFFD) ||
      in_range(cp, 0x50000, 0x5FFFD) ||
      in_range(cp, 0x60000, 0x6FFFD) ||
      in_range(cp, 0x70000, 0x7FFFD) ||
      in_range(cp, 0x80000, 0x8FFFD) ||
      in_range(cp, 0x90000, 0x9FFFD) ||
      in_range(cp, 0xA0000, 0xAFFFD) ||
      in_range(cp, 0xB0000, 0xBFFFD) ||
      in_range(cp, 0xC0000, 0xCFFFD) ||
      in_range(cp, 0xD0000, 0xDFFFD) ||
      in_range(cp, 0xE0000, 0xEFFFD);
}

bool is_digit(int cp)
{
  return cp >= '0' && cp <= '9';
}

bool is_oct_digit(int cp)
{
  return cp >= '0' && cp <= '7';
}

bool is_hex_digit(int cp)
{
  return (cp >= '0' && cp <= '9') ||
      (cp >= 'a' && cp <= 'f') ||
      (cp >= 'A' && cp <= 'F');
}

int hex_value(int cp)
{
  if(cp >= '0' && cp <= '9') {
    return cp - '0';
  }
  if(cp >= 'a' && cp <= 'f') {
    return cp - 'a' + 10;
  }
  if(cp >= 'A' && cp <= 'F') {
    return cp - 'A' + 10;
  }
  throw logic_error("hex_value on non-hex character");
}

bool is_ascii_identifier_start(int cp)
{
  return (cp >= 'a' && cp <= 'z') ||
      (cp >= 'A' && cp <= 'Z') ||
      cp == '_';
}

bool is_identifier_start_cp(int cp)
{
  if(is_ascii_identifier_start(cp)) {
    return true;
  }
  if(cp < 0x80) {
    return false;
  }
  return is_annex_e1(cp) && !is_annex_e2(cp);
}

bool is_identifier_body_cp(int cp)
{
  if(is_ascii_identifier_start(cp) || is_digit(cp)) {
    return true;
  }
  if(cp < 0x80) {
    return false;
  }
  return (is_annex_e1(cp) && !is_annex_e2(cp)) || is_annex_e2(cp);
}

bool is_space_no_newline(int cp)
{
  return cp == ' ' || cp == '\t' || cp == '\v' || cp == '\f' || cp == '\r';
}

bool is_simple_escape(int cp)
{
  switch(cp) {
    case '\'':
    case '"':
    case '?':
    case '\\':
    case 'a':
    case 'b':
    case 'f':
    case 'n':
    case 'r':
    case 't':
    case 'v':
      return true;
    default:
      return false;
  }
}

bool is_identifier_like_operator(const string & data)
{
  static const char * const names[] = {
    "new", "delete", "and", "and_eq", "bitand", "bitor", "compl",
    "not", "not_eq", "or", "or_eq", "xor", "xor_eq"
  };
  for(size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
    if(data == names[i]) {
      return true;
    }
  }
  return false;
}

class Tokenizer
{
public:
  Tokenizer(const vector<SourceChar> & source,
            const vector<TextChar> & text,
            IPPTokenStream & output)
      : source_(source), text_(text), output_(output),
        source_size_(source.size()), text_size_(text.size()), pos_(0),
        header_state_(HeaderState::AtLineStart)
  {
  }

  void run()
  {
    while(pos_ < text_size_) {
      if(scan_newline() || scan_whitespace_or_comment() ||
         scan_header_name() || scan_literal() || scan_identifier() ||
         scan_pp_number() || scan_operator()) {
        continue;
      }
      scan_non_whitespace();
    }
    output_.emit_eof();
  }

private:
  const vector<SourceChar> & source_;
  const vector<TextChar> & text_;
  IPPTokenStream & output_;
  size_t source_size_;
  size_t text_size_;
  size_t pos_;
  HeaderState header_state_;

  string error_at(size_t index, const string & message) const
  {
    if(index < text_size_) {
      return location_message(text_[index].line, text_[index].column, message);
    }
    if(!text_.empty()) {
      return location_message(text_.back().line, text_.back().column, message);
    }
    return location_message(1, 1, message);
  }

  void note_location(size_t index)
  {
    if(index < text_size_) {
      output_.note_source_location(text_[index].line, text_[index].column);
    } else if(!text_.empty()) {
      output_.note_source_location(text_.back().line, text_.back().column);
    } else {
      output_.note_source_location(1, 1);
    }
  }

  bool decode_ucn_at(size_t index, LogicalChar & out, bool diagnose = true) const
  {
    if(index + 1 >= text_size_ || text_[index].cp != '\\') {
      return false;
    }
    const int marker = text_[index + 1].cp;
    const size_t digits = marker == 'u' ? 4 : marker == 'U' ? 8 : 0;
    if(digits == 0) {
      return false;
    }
    if(index + 2 + digits > text_size_) {
      return false;
    }
    int cp = 0;
    for(size_t i = 0; i < digits; ++i) {
      const int digit = text_[index + 2 + i].cp;
      if(!is_hex_digit(digit)) {
        return false;
      }
      cp = (cp << 4) | hex_value(digit);
    }
    if(cp > 0x10FFFF) {
      if(!diagnose) {
        return false;
      }
      const size_t error_index = index + 1 + digits;
      throw runtime_error(error_at(error_index, "Invalid 32 bit value for utf8"));
    }
    out.cp = cp;
    out.width = 2 + digits;
    return true;
  }

  LogicalChar logical_at(size_t index) const
  {
    LogicalChar out;
    if(index >= text_size_) {
      out.cp = -1;
      out.width = 0;
      return out;
    }
    const int cp = text_[index].cp;
    if(cp == '\\' && decode_ucn_at(index, out)) {
      return out;
    }
    out.cp = cp;
    out.width = 1;
    return out;
  }

  LogicalChar comment_logical_at(size_t index) const
  {
    LogicalChar out;
    if(index >= text_size_) {
      out.cp = -1;
      out.width = 0;
      return out;
    }
    const int cp = text_[index].cp;
    if(cp == '\\' && decode_ucn_at(index, out, false)) {
      return out;
    }
    out.cp = cp;
    out.width = 1;
    return out;
  }

  void append_logical(size_t index, LogicalChar logical, string & data) const
  {
    (void)index;
    append_utf8(logical.cp, data);
  }

  bool logical_matches_ascii(size_t index,
                             const string & value,
                             size_t & consumed) const
  {
    size_t cursor = index;
    for(size_t i = 0; i < value.size(); ++i) {
      LogicalChar logical = logical_at(cursor);
      if(logical.cp != static_cast<unsigned char>(value[i])) {
        return false;
      }
      cursor += logical.width;
    }
    consumed = cursor - index;
    return true;
  }

  bool logical_matches_ascii(size_t index,
                             const char * value,
                             size_t & consumed) const
  {
    size_t cursor = index;
    for(size_t i = 0; value[i] != '\0'; ++i) {
      LogicalChar logical = logical_at(cursor);
      if(logical.cp != static_cast<unsigned char>(value[i])) {
        return false;
      }
      cursor += logical.width;
    }
    consumed = cursor - index;
    return true;
  }

  bool logical_pair(size_t index, int first, int second, size_t & consumed) const
  {
    LogicalChar a = logical_at(index);
    if(a.cp != first) {
      return false;
    }
    LogicalChar b = logical_at(index + a.width);
    if(b.cp != second) {
      return false;
    }
    consumed = a.width + b.width;
    return true;
  }

  bool comment_logical_pair(size_t index,
                            int first,
                            int second,
                            size_t & consumed) const
  {
    LogicalChar a = comment_logical_at(index);
    if(a.cp != first) {
      return false;
    }
    LogicalChar b = comment_logical_at(index + a.width);
    if(b.cp != second) {
      return false;
    }
    consumed = a.width + b.width;
    return true;
  }

  bool logical_space_no_newline(size_t index, size_t & width) const
  {
    LogicalChar logical = logical_at(index);
    if(!is_space_no_newline(logical.cp)) {
      return false;
    }
    width = logical.width;
    return true;
  }

  string source_slice(size_t first, size_t last) const
  {
    string data;
    for(size_t i = first; i < last && i < source_size_; ++i) {
      append_utf8(source_[i].cp, data);
    }
    return data;
  }

  void note_non_whitespace_token(const string & type, const string & data)
  {
    if(header_state_ == HeaderState::AtLineStart) {
      header_state_ = (type == "op" && (data == "#" || data == "%:"))
          ? HeaderState::AfterHash
          : HeaderState::Normal;
      return;
    }
    if(header_state_ == HeaderState::AfterHash) {
      header_state_ = (type == "identifier" && data == "include")
          ? HeaderState::AfterInclude
          : HeaderState::Normal;
      return;
    }
    header_state_ = HeaderState::Normal;
  }

  bool scan_newline()
  {
    LogicalChar logical = logical_at(pos_);
    if(logical.cp != '\n') {
      return false;
    }
    note_location(pos_);
    pos_ += logical.width;
    output_.emit_new_line();
    header_state_ = HeaderState::AtLineStart;
    return true;
  }

  bool scan_whitespace_or_comment()
  {
    size_t width = 0;
    if(!logical_space_no_newline(pos_, width) && !starts_comment(pos_, width)) {
      return false;
    }
    const size_t start = pos_;
    bool consumed = false;
    while(pos_ < text_size_) {
      if(logical_space_no_newline(pos_, width)) {
        consumed = true;
        pos_ += width;
        continue;
      }
      if(starts_line_comment(pos_, width)) {
        consumed = true;
        pos_ += width;
        while(pos_ < text_size_ && text_[pos_].cp != '\n') {
          LogicalChar logical = comment_logical_at(pos_);
          if(logical.cp == '\n') {
            break;
          }
          pos_ += logical.width;
        }
        continue;
      }
      if(starts_block_comment(pos_, width)) {
        consumed = true;
        consume_block_comment();
        continue;
      }
      break;
    }
    if(consumed) {
      note_location(start);
      output_.emit_whitespace_sequence();
    }
    return consumed;
  }

  bool starts_comment(size_t index, size_t & consumed) const
  {
    return starts_line_comment(index, consumed) ||
        starts_block_comment(index, consumed);
  }

  bool starts_line_comment(size_t index, size_t & consumed) const
  {
    return logical_pair(index, '/', '/', consumed);
  }

  bool starts_block_comment(size_t index, size_t & consumed) const
  {
    return logical_pair(index, '/', '*', consumed);
  }

  void consume_block_comment()
  {
    const size_t start = pos_;
    size_t width = 0;
    starts_block_comment(pos_, width);
    pos_ += width;
    while(pos_ < text_size_) {
      if(comment_logical_pair(pos_, '*', '/', width)) {
        pos_ += width;
        return;
      }
      LogicalChar logical = comment_logical_at(pos_);
      pos_ += logical.width;
    }
    throw runtime_error(error_at(start, "Unterminated comment"));
  }

  bool scan_header_name()
  {
    if(header_state_ != HeaderState::AfterInclude) {
      return false;
    }
    LogicalChar logical = logical_at(pos_);
    if(logical.cp == '<') {
      return scan_angle_header_name();
    }
    if(logical.cp == '"') {
      return scan_quote_header_name();
    }
    return false;
  }

  bool scan_angle_header_name()
  {
    const size_t start = pos_;
    string data;
    LogicalChar logical = logical_at(pos_);
    append_logical(pos_, logical, data);
    pos_ += logical.width;
    while(pos_ < text_size_) {
      logical = logical_at(pos_);
      if(logical.cp == '\n') {
        break;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
      if(logical.cp == '>') {
        note_location(start);
        output_.emit_header_name(data);
        header_state_ = HeaderState::Normal;
        return true;
      }
    }
    pos_ = start;
    return false;
  }

  bool scan_quote_header_name()
  {
    const size_t start = pos_;
    string data;
    LogicalChar logical = logical_at(pos_);
    append_logical(pos_, logical, data);
    pos_ += logical.width;
    while(pos_ < text_size_) {
      logical = logical_at(pos_);
      if(logical.cp == '\n') {
        break;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
      if(logical.cp == '"') {
        note_location(start);
        output_.emit_header_name(data);
        header_state_ = HeaderState::Normal;
        return true;
      }
    }
    pos_ = start;
    return false;
  }

	  bool scan_literal()
	  {
	    LogicalChar first = logical_at(pos_);
	    switch(first.cp) {
	      case 'u':
	      case 'U':
	      case 'L':
	      case 'R':
	      case '"':
	      case '\'':
	        break;
	      default:
	        return false;
	    }
	    return scan_raw_string() || scan_string() || scan_character();
	  }

  bool scan_raw_string()
  {
    const size_t start = pos_;
    string data;
    size_t prefix_width = 0;
    if(!raw_prefix(data, prefix_width)) {
      return false;
    }
    const size_t open_source = source_index_at_text_position(pos_ + prefix_width);
    const size_t source_end = parse_raw_source_end(open_source);
    pos_ = text_position_after_source(source_end);
    data += source_slice(open_source, source_end);
    append_identifier_suffix(data);
    note_location(start);
    emit_string_token(data);
    return true;
  }

  bool raw_prefix(string & data, size_t & consumed) const
  {
    static const char * const prefixes[] = { "u8R\"", "uR\"", "UR\"", "LR\"", "R\"" };
    return match_logical_prefix(prefixes,
                                sizeof(prefixes) / sizeof(prefixes[0]),
                                data,
                                consumed);
  }

  bool match_logical_prefix(const char * const * prefixes,
                            size_t prefix_count,
                            string & data,
                            size_t & consumed) const
  {
    for(size_t i = 0; i < prefix_count; ++i) {
      if(!logical_matches_ascii(pos_, prefixes[i], consumed)) {
        continue;
      }
      data.clear();
      size_t cursor = pos_;
      while(cursor < pos_ + consumed) {
        LogicalChar logical = logical_at(cursor);
        append_logical(cursor, logical, data);
        cursor += logical.width;
      }
      return true;
    }
    return false;
  }

  size_t source_index_at_text_position(size_t index) const
  {
    if(index < text_size_) {
      return text_[index].source_index;
    }
    return source_size_;
  }

  size_t parse_raw_source_end(size_t open_search) const
  {
    size_t open = open_search;
    vector<int> delimiter;
    while(open < source_size_ && source_[open].cp != '(') {
      if(delimiter.size() == 16) {
        throw runtime_error(general_message("raw string delimiter too long"));
      }
      if(!is_raw_delimiter_char(source_[open].cp)) {
        throw runtime_error(general_message("unterminated raw string literal"));
      }
      delimiter.push_back(source_[open].cp);
      ++open;
    }
    if(open >= source_size_) {
      throw runtime_error(general_message("unterminated raw string literal"));
    }
    for(size_t i = open + 1; i < source_size_; ++i) {
      if(source_[i].cp == ')' && raw_close_matches(i, delimiter)) {
        return i + delimiter.size() + 2;
      }
    }
    throw runtime_error(general_message("unterminated raw string literal"));
  }

  bool is_raw_delimiter_char(int cp) const
  {
    return cp != ' ' && cp != '(' && cp != ')' && cp != '\\' &&
        cp != '\t' && cp != '\v' && cp != '\f' && cp != '\n';
  }

  bool raw_close_matches(size_t close, const vector<int> & delimiter) const
  {
    if(close + delimiter.size() + 1 >= source_size_) {
      return false;
    }
    for(size_t i = 0; i < delimiter.size(); ++i) {
      if(source_[close + 1 + i].cp != delimiter[i]) {
        return false;
      }
    }
    return source_[close + 1 + delimiter.size()].cp == '"';
  }

  size_t text_position_after_source(size_t source_end) const
  {
    size_t i = pos_;
    while(i < text_size_ && !text_[i].synthetic &&
          text_[i].source_index < source_end) {
      ++i;
    }
    return i;
  }

  bool scan_string()
  {
    const size_t start = pos_;
    string data;
    size_t prefix_width = 0;
    if(!string_prefix(data, prefix_width)) {
      return false;
    }
    pos_ += prefix_width;
    scan_quoted_body('"', "Unterminated string literal", data);
    append_identifier_suffix(data);
    note_location(start);
    emit_string_token(data);
    return true;
  }

  bool string_prefix(string & data, size_t & consumed) const
  {
    static const char * const prefixes[] = { "u8\"", "u\"", "U\"", "L\"", "\"" };
    return match_logical_prefix(prefixes,
                                sizeof(prefixes) / sizeof(prefixes[0]),
                                data,
                                consumed);
  }

  bool scan_character()
  {
    const size_t start = pos_;
    string data;
    size_t prefix_width = 0;
    if(!character_prefix(data, prefix_width)) {
      return false;
    }
    pos_ += prefix_width;
    scan_quoted_body('\'', "Unterminated character literal", data);
    append_identifier_suffix(data);
    note_location(start);
    emit_character_token(data);
    return true;
  }

  bool character_prefix(string & data, size_t & consumed) const
  {
    static const char * const prefixes[] = { "u'", "U'", "L'", "'" };
    return match_logical_prefix(prefixes,
                                sizeof(prefixes) / sizeof(prefixes[0]),
                                data,
                                consumed);
  }

  void scan_quoted_body(int close_cp,
                        const string & error_message,
                        string & data)
  {
    while(pos_ < text_size_) {
      LogicalChar logical = logical_at(pos_);
      if(logical.cp == close_cp) {
        append_logical(pos_, logical, data);
        pos_ += logical.width;
        return;
      }
      if(logical.cp == '\n') {
        throw runtime_error(error_at(pos_, error_message));
      }
      if(logical.cp == '\\') {
        consume_escape_sequence(data);
        continue;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
    }
    throw runtime_error(error_at(pos_, error_message));
  }

  void consume_escape_sequence(string & data)
  {
    LogicalChar slash = logical_at(pos_);
    append_logical(pos_, slash, data);
    pos_ += slash.width;
    if(pos_ >= text_size_) {
      throw runtime_error(error_at(pos_, "Invalid escape sequence"));
    }
    LogicalChar escaped = logical_at(pos_);
    if(escaped.cp == '\n') {
      throw runtime_error(error_at(pos_, "Invalid escape sequence"));
    }
    if(is_simple_escape(escaped.cp)) {
      append_logical(pos_, escaped, data);
      pos_ += escaped.width;
      return;
    }
    if(is_oct_digit(escaped.cp)) {
      consume_octal_escape(data);
      return;
    }
    if(escaped.cp == 'x') {
      consume_hex_escape(data);
      return;
    }
    throw runtime_error(error_at(pos_, "Invalid escape sequence"));
  }

  void consume_octal_escape(string & data)
  {
    for(size_t count = 0; count < 3 && pos_ < text_size_; ++count) {
      LogicalChar logical = logical_at(pos_);
      if(!is_oct_digit(logical.cp)) {
        break;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
    }
  }

  void consume_hex_escape(string & data)
  {
    LogicalChar x = logical_at(pos_);
    append_logical(pos_, x, data);
    pos_ += x.width;
    if(pos_ >= text_size_ || !is_hex_digit(logical_at(pos_).cp)) {
      throw runtime_error(error_at(pos_, "invalid hex escape sequence"));
    }
    while(pos_ < text_size_) {
      LogicalChar logical = logical_at(pos_);
      if(!is_hex_digit(logical.cp)) {
        break;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
    }
  }

  void append_identifier_suffix(string & data)
  {
    if(pos_ >= text_size_) {
      return;
    }
    LogicalChar first = logical_at(pos_);
    if(!is_identifier_start_cp(first.cp)) {
      return;
    }
    while(pos_ < text_size_) {
      LogicalChar logical = logical_at(pos_);
      if(!is_identifier_body_cp(logical.cp)) {
        return;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
    }
  }

  void emit_string_token(const string & data)
  {
    if(has_user_defined_suffix(data, '"')) {
      output_.emit_user_defined_string_literal(data);
    } else {
      output_.emit_string_literal(data);
    }
    note_non_whitespace_token("literal", data);
  }

  void emit_character_token(const string & data)
  {
    if(has_user_defined_suffix(data, '\'')) {
      output_.emit_user_defined_character_literal(data);
    } else {
      output_.emit_character_literal(data);
    }
    note_non_whitespace_token("literal", data);
  }

  bool has_user_defined_suffix(const string & data, char quote) const
  {
    return !data.empty() && data[data.size() - 1] != quote;
  }

  bool scan_identifier()
  {
    LogicalChar first = logical_at(pos_);
    if(!is_identifier_start_cp(first.cp)) {
      return false;
    }
    const size_t start = pos_;
    string data;
    while(pos_ < text_size_) {
      LogicalChar logical = logical_at(pos_);
      if(!is_identifier_body_cp(logical.cp)) {
        break;
      }
      append_logical(pos_, logical, data);
      pos_ += logical.width;
    }
    note_location(start);
    if(is_identifier_like_operator(data)) {
      output_.emit_preprocessing_op_or_punc(data);
      note_non_whitespace_token("op", data);
    } else {
      output_.emit_identifier(data);
      note_non_whitespace_token("identifier", data);
    }
    return true;
  }

  bool scan_pp_number()
  {
    if(!starts_pp_number()) {
      return false;
    }
    const size_t start = pos_;
    string data;
    int previous = -1;
    while(pos_ < text_size_) {
      LogicalChar logical = logical_at(pos_);
      if(is_digit(logical.cp) || logical.cp == '.' ||
         is_identifier_body_cp(logical.cp)) {
        append_logical(pos_, logical, data);
        previous = logical.cp;
        pos_ += logical.width;
        continue;
      }
      if((logical.cp == '+' || logical.cp == '-') &&
         (previous == 'e' || previous == 'E' ||
          previous == 'p' || previous == 'P')) {
        append_logical(pos_, logical, data);
        previous = logical.cp;
        pos_ += logical.width;
        continue;
      }
      break;
    }
    note_location(start);
    output_.emit_pp_number(data);
    note_non_whitespace_token("pp-number", data);
    return true;
  }

  bool starts_pp_number() const
  {
    if(pos_ >= text_size_) {
      return false;
    }
    LogicalChar first = logical_at(pos_);
    if(is_digit(first.cp)) {
      return true;
    }
    if(first.cp != '.') {
      return false;
    }
    LogicalChar second = logical_at(pos_ + first.width);
    return is_digit(second.cp);
  }

	  bool scan_operator()
	  {
	    if(scan_angle_colon_exception()) {
	      return true;
	    }
	    LogicalChar first = logical_at(pos_);
	    switch(first.cp) {
	      case '%':
	        return scan_operator_token("%:%:") || scan_operator_token("%>") ||
	            scan_operator_token("%:") || scan_operator_token("%=") ||
	            scan_operator_token("%");
	      case '>':
	        return scan_operator_token(">>=") || scan_operator_token(">>") ||
	            scan_operator_token(">=") || scan_operator_token(">");
	      case '<':
	        return scan_operator_token("<<=") || scan_operator_token("<:") ||
	            scan_operator_token("<%") || scan_operator_token("<<") ||
	            scan_operator_token("<=") || scan_operator_token("<");
	      case '-':
	        return scan_operator_token("->*") || scan_operator_token("-=") ||
	            scan_operator_token("--") || scan_operator_token("->") ||
	            scan_operator_token("-");
	      case '.':
	        return scan_operator_token("...") || scan_operator_token(".*") ||
	            scan_operator_token(".");
	      case '#':
	        return scan_operator_token("##") || scan_operator_token("#");
	      case ':':
	        return scan_operator_token(":>") || scan_operator_token("::") ||
	            scan_operator_token(":");
	      case '+':
	        return scan_operator_token("+=") || scan_operator_token("++") ||
	            scan_operator_token("+");
	      case '*':
	        return scan_operator_token("*=") || scan_operator_token("*");
	      case '/':
	        return scan_operator_token("/=") || scan_operator_token("/");
	      case '^':
	        return scan_operator_token("^=") || scan_operator_token("^");
	      case '&':
	        return scan_operator_token("&=") || scan_operator_token("&&") ||
	            scan_operator_token("&");
	      case '|':
	        return scan_operator_token("|=") || scan_operator_token("||") ||
	            scan_operator_token("|");
	      case '=':
	        return scan_operator_token("==") || scan_operator_token("=");
	      case '!':
	        return scan_operator_token("!=") || scan_operator_token("!");
	      case '{': return scan_operator_token("{");
	      case '}': return scan_operator_token("}");
	      case '[': return scan_operator_token("[");
	      case ']': return scan_operator_token("]");
	      case '(': return scan_operator_token("(");
	      case ')': return scan_operator_token(")");
	      case ';': return scan_operator_token(";");
	      case '?': return scan_operator_token("?");
	      case '~': return scan_operator_token("~");
	      case ',': return scan_operator_token(",");
	      default:
	        return false;
	    }
	  }

	  bool scan_operator_token(const char * op)
	  {
	    size_t consumed = 0;
	    if(!logical_matches_ascii(pos_, op, consumed)) {
	      return false;
	    }
	    const size_t start = pos_;
	    pos_ += consumed;
	    note_location(start);
	    string data(op);
	    output_.emit_preprocessing_op_or_punc(data);
	    note_non_whitespace_token("op", data);
	    return true;
	  }

	  bool scan_angle_colon_exception()
  {
    size_t consumed = 0;
    if(!logical_matches_ascii(pos_, "<::", consumed)) {
      return false;
    }
    LogicalChar fourth = logical_at(pos_ + consumed);
    if(fourth.cp == ':' || fourth.cp == '>') {
      return false;
    }
    LogicalChar first = logical_at(pos_);
    const size_t start = pos_;
    pos_ += first.width;
    note_location(start);
    output_.emit_preprocessing_op_or_punc("<");
    note_non_whitespace_token("op", "<");
    return true;
  }

  void scan_non_whitespace()
  {
    const size_t start = pos_;
    LogicalChar logical = logical_at(pos_);
    if(logical.cp == '"' || logical.cp == '\'') {
      throw runtime_error(error_at(pos_, "Invalid preprocessing token"));
    }
    string data;
    append_utf8(logical.cp, data);
    pos_ += logical.width;
    note_location(start);
    output_.emit_non_whitespace_char(data);
    note_non_whitespace_token("non-whitespace", data);
  }
};

}  // namespace

void run_pptoken(istream & in, IPPTokenStream & output)
{
  ostringstream buffer;
  buffer << in.rdbuf();
  const vector<SourceChar> source =
      decode_source(sanitize_invalid_comment_bytes(buffer.str()));
  const vector<TextChar> text = translated_text(source);
  Tokenizer(source, text, output).run();
}

}  // namespace pptoken
