#include "Matches.h"
#include "../std/utility.h"

using namespace std;

bool Matches::empty() const
{
    return indices.size() < 2;
}

int Matches::operator-(const Matches &rhs) const
{
    int cmp = scan_length * (int)indices.size() - rhs.scan_length * (int)rhs.indices.size();
    if (cmp)
        return cmp;
    // if the areas are the same, then compare the scan_length: the larger, the better
    return scan_length - rhs.scan_length;
}

bool Matches::overlap(const Matches &rhs) const
{
    for (auto start : rhs.indices)
    {
        if (overlap(start, start + rhs.scan_length))
            return true;
    }
    return false;
}

bool Matches::overlap(int start, int end) const
{
    int j = binary_search(indices, start);
    if (j && start < indices[j - 1] + scan_length)
        return true;
    if (j < indices.size())
        return indices[j] == start || indices[j] < end;
    return false;
}

std::ostream &operator<<(std::ostream &cout, const Matches &rhs)
{
    return cout << "{\"" << rhs.scan_length << "\": " << rhs.indices << "}";
}
