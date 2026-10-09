#pragma once
#include <iostream>
#include <vector>
using std::vector;
#include "HashCode.h"

// record the indices of the starting index of the matching pattern that is of scan_length, as well as their hash code
struct Matches {
    // the length of the pattern
    int scan_length;
    // the hash code of the pattern, all the patterns have the same hash code since they are the same
    HashCode hashCode;
    // the starting indices of the matching pattern
    vector<int> indices;

    bool overlap(const Matches &rhs) const;
    bool overlap(int start, int end) const;
    friend std::ostream& operator <<(std::ostream &cout, const Matches &p);
    bool empty() const;

    int operator-(const Matches &rhs) const;
};
