#pragma once
#include <array>
using std::array;
#include "../std/utility.h"
#include "Matches.h"


class RabinKarp {
public:
    RabinKarp(const string& text, int scan_length=8);

    // expand the oldMatches by doubling the scan_length
    vector<Matches> expand(vector<Matches> &oldMatches) const;

    // try to extend scan_length of matches by 8 bytes
    Matches extend_bytes(Matches matches) const;

    // try to extend scan_length of matches by 1 byte
    Matches extend_byte(Matches matches) const;

    // return a list of Matches
    vector<Matches> redundancy_detect();

    // Search for the pattern in the text, return a list of lists of the starting indices of the duplicated pattern grouped by the same pattern
    vector<Matches> initial_detect();
    void debug(const vector<Matches> &matches) const;

    void test();
    vector<int> &physic2logic(vector<int> &indices) const;
    void init_physicOffset();
private:
    const string &text;
    int scan_length;
    // the hashCode stores the initial hash of the substring of fixed-size scan_length = 8
    vector<HashCode> hashCode;
    // the hashCode stores the dynamic hash of the substring of variable-sized scan_length
    dict<int, HashCode> hashDict;
    vector<std::pair<int, int>> physicOffset;
    int physic2logic(int physicOffset) const;

    // Compute the hash for the next window using rolling hash technique
    void rolling_hash(HashCode &window_hash, const HashCode &h, int i) const;
    bool matches(int i, int j, int scan_length) const;

    // return a hashTable maps an integer index to a HashCode object that represents the String hash code with scan_length
    void create_hash_table_for_double_hashing(const vector<Matches> &matches);

    // inner loop to find the optimal expansion of a match
    void try_optimal_expansion(const Matches &match, int i, vector<Matches> &optimalCollector) const;

    // precondition: prev_end exists in hashDict
    void find_optimal_expansion(const Matches &match, vector<Matches> &optimalCollector) const;
    string substr(const Matches &match) const;
    string info(const Matches &match) const;
    double max_repetition_distance(int scan_length) const;
    vector<vector<int>> disentangle(const vector<int> &list) const;
    int post_condition(const vector<int> &list) const;
};