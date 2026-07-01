# string literal converts through std::string for const reference parameter
#include <sstream>
#include <stdexcept>
#include <string>

using namespace std;

string location_message(int line, int column, const string& message)
{
	ostringstream out;
	out << line << ":" << column << ":" << message;
	return out.str();
}

void test()
{
	throw runtime_error(location_message(1, 1, "Invalid utf-8 character"));
}
