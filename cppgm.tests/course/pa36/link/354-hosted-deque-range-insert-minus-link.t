# hosted deque range insert uses iterator minus
#include <deque>
#include <vector>

int main()
{
  std::deque<int> pending;
  std::vector<int> calls;
  calls.push_back(1);
  calls.push_back(2);

  pending.insert(pending.end(), calls.begin(), calls.end());

  return pending.size() == 2 ? 0 : 1;
}
