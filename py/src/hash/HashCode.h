#pragma once
#include <vector>
#include <string>
using std::vector;
using std::string;

using hash_t = unsigned long long;

// a HashCode represent a nonnegative integer within [0, MersenneMask), its high 3 bits are all zeros.
struct HashCode {
    // default constructor
    HashCode();
    // m represents MersenneBit
    // ∀ n m : ℕ, n ≡ n / 2 ^ m + n % 2 ^ m [MOD 2 ^ m - 1]
    // http://www.lemma.cn/lean/?module=Algebra.ModEq__AddDiv__Mod
    HashCode(hash_t hash);
    HashCode(const __uint128_t &hash);

    // initialize the hash code with the a string within the limit of size
    HashCode(const string &s, int size);

    // initialize the hash code with the a string
    HashCode(const string &s);

    // construct a HashCode with a given HashCode and a char, effectively performing : ((n << BaseBit) | c) % MersenneMask
    // b represents BaseBit
    // b ≤ m ⇒ n * 2 ^ b ≡ n / 2 ^ (m - b) + n % 2 ^ (m - b) * 2 ^ b [MOD 2 ^ m - 1]
    // http://www.lemma.cn/lean/?module=Algebra.ModEq__AddDiv__MulMod.of.Le
    HashCode(const HashCode &bigInt, unsigned char c);
    
    HashCode operator+(const HashCode &rhs) const;

    HashCode &operator+=(const HashCode &rhs);
    
    HashCode operator-(const HashCode &rhs) const;

    HashCode operator * (char c) const;
    
    bool operator==(const HashCode &rhs) const;
    
    // compute: (*this * (2 ^ (8 * exponent))) % MersennePrime
    HashCode shl(int exponent) const;

    friend std::ostream& operator <<(std::ostream &cout, const HashCode &p);

    hash_t hash;
};