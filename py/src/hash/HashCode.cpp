#include <string.h>
#include <iomanip>
#include "HashCode.h"
using namespace std;

// Base 256 (1 << 8) for the hash function
#define BaseBit 8
// A Mersenne prime number for modulo operation
#define MersenneBit 61

const int ShiftLeftBit = MersenneBit - BaseBit;
const hash_t ShiftLeftMask = (1uLL << ShiftLeftBit) - 1;
const hash_t MersenneMask = (1uLL << MersenneBit) - 1; // A Mersenne prime number for modulo operation

HashCode::HashCode() : hash(1uLL) {}

HashCode::HashCode(hash_t bigInt) {
    // the high 3 bits of the bigInt, subject to: high ∈ [0, 7]
    auto high = bigInt >> MersenneBit;
    // the low 61 bits of the bigInt, subject to: low ∈ [0, MersenneMask]
    auto low = bigInt & MersenneMask;
    // the sum of the low, mid, and high, subject to: sum ∈ [0, MersenneMask + 7] ⊆ [0, 2 ^ 64)
    auto sum = low + high;
    // sum / MersenneMask ∈ [0, 1 + 7 / MersenneMask]
    if (sum >= MersenneMask)
        sum -= MersenneMask;
    hash = sum;
}

HashCode::HashCode(const string &s, int size) : hash(0)
{
    for (int i = 0; i < size; ++i)
        *this = HashCode(*this, s[i]);
}

HashCode::HashCode(const string &s) : HashCode(s, s.length()) {}

HashCode HashCode::operator+(const HashCode &rhs) const
{
    // the addition of two hash codes under modulo MersenneMask will not overflow
    // call the constructor : HashCode(hash_t hash)
    return hash + rhs.hash;
}

HashCode &HashCode::operator+=(const HashCode &rhs)
{
    return *this = *this + rhs;
}

HashCode HashCode::operator-(const HashCode &rhs) const
{
    // call the copy constructor
    return *this + (MersenneMask - rhs.hash);
}

HashCode::HashCode(const HashCode &bigInt, unsigned char c)
{
    // precondition: bigInt.hash ∈ [0, MersenneMask - 1]
    // the high 11 bits of the bigInt, since the left 3 bits are zero, we have: high ∈ [0, 255]
    auto high = bigInt.hash >> ShiftLeftBit;
    // the low 53 bits of the bigInt, subject to: low ∈ [0, 2 ^ 53 -1]
    auto low = bigInt.hash & ShiftLeftMask;
    // low *= 256, subject to: low ∈ [0, (2 ^ 53 -1) * 2 ^ 8] = [0, MersenneMask - 255]
    low = low << BaseBit | c;
    // the sum of the low, high and c, subject to: sum ∈ [0, MersenneMask + 255]
    auto sum = high + low;
    if (sum >= MersenneMask)
        sum -= MersenneMask;
    hash = sum;
}

HashCode HashCode::operator*(char c) const
{
    // call the constructor : HashCode(const __uint128_t &hash);
    return (__uint128_t)hash * (unsigned char)c;
}

HashCode HashCode::shl(int exponent) const
{
    exponent *= BaseBit;
    exponent %= MersenneBit; // now 0 <= exponent < 61
    // hash * 2 ^ (8 * exponent) % MersenneMask = 
    // hash * 2 ^ (61 * q + r) % MersenneMask = 
    // hash * 2 ^ (61 * q) * 2 ^ r % MersenneMask = 
    // hash * (2 ^ 61) ^ q * 2 ^ r % MersenneMask = 
    // hash * 1 ^ q * 2 ^ r % MersenneMask = 
    // hash * 2 ^ r % MersenneMask = 
    // (hash << r) % MersenneMask
    return (__uint128_t)hash << exponent;
}

bool HashCode::operator==(const HashCode &rhs) const
{
    return hash == rhs.hash;
}

HashCode::HashCode(const __uint128_t &bigInt) {
    // the high 6 bits of the bigInt, subject to: high ∈ [0, 127]
    auto high = bigInt >> (MersenneBit << 1);
    // the middle 61 bits of the bigInt, subject to: mid ∈ [0, MersenneMask]
    auto mid = (bigInt >> MersenneBit) & MersenneMask;
    // the low 61 bits of the bigInt, subject to: low ∈ [0, MersenneMask]
    auto low = bigInt & MersenneMask;
    // the sum of the low, mid, and high, subject to: sum ∈ [0, 2 ^ MersenneMask + 127] ⊆ [0, 2 ^ 64)
    auto sum = low + mid + high;
    // maximum 2 times of subtraction, since: sum / MersenneMask ∈ [0, 2 + 127 / MersenneMask]
    if (sum >= MersenneMask) {
        sum -= MersenneMask;
        if (sum >= MersenneMask)
           sum -= MersenneMask;
    }
    hash = sum;
}


std::ostream &operator<<(std::ostream &cout, const HashCode &rhs)
{
    // auto old_flags = cout.flags(); // Save original flags
    // cout << std::uppercase << std::hex << rhs.hash << endl;
    // cout.flags(old_flags); // Restore original flags
    return cout << rhs.hash;
}
