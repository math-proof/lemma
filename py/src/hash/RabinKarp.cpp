#include <string.h>
#include <cmath>
#include <algorithm>
#include <iostream>
#include "RabinKarp.h"
using namespace std;

RabinKarp::RabinKarp(const string &text, int scan_length) : 
    text(text),
    scan_length(scan_length),
    // in theory, hashCode.size() = text.size() - scan_length + 1, but to prevent out of bound error, I deliberately set it to be text.size() - scan_length + 2
    hashCode(max((int)text.size() - scan_length + 2, 0))
{
}

void RabinKarp::rolling_hash(HashCode &window_hash, const HashCode &h, int i) const
{
    if (i + scan_length < text.size())
        window_hash = HashCode(window_hash - (h * text[i]), text[i + scan_length]);
}

bool RabinKarp::matches(int i, int j, int scan_length) const
{
    return !strncmp(&text[i], &text[j], scan_length);
}

int RabinKarp::post_condition(const vector<int> &list) const {
    for (int i : range(1, list.size())) {
        if (list[i] - list[i - 1] < scan_length) {
            print("list[", i, "] - list[", i - 1, "] =", list[i] - list[i - 1]);
            return i;
        }
    }
    return 0;
}

vector<vector<int>> RabinKarp::disentangle(const vector<int> &list) const {
    vector<int> deleteIndices;
    int currentIndex = 0;
    for (int i : range(1, list.size())) {
        if (list[i] - list[currentIndex] < scan_length)
            deleteIndices.push_back(i);
        else
            currentIndex = i;
    }
    if (deleteIndices.empty())
        return {std::move(list)};
    auto [undisentangled, disentangled] = array_split(list, std::move(deleteIndices));
    auto array = disentangle(undisentangled);
    array.push_back(std::move(disentangled));
    return array;
}

vector<Matches> RabinKarp::initial_detect()
{
    int n = text.size();
    if (n < scan_length)
        return {};

    unordered_map<hash_t, vector<vector<int>>> hashDict;
    // Compute the hash of the pattern and the first window in the text
    HashCode window_hash(text, scan_length);
    auto h = HashCode().shl(scan_length - 1);

    // Slide the window over the text
    for (int i : range(0, n - scan_length + 1))
    {
        hash_t hash = window_hash.hash;
        // cache the hash code for later processing
        hashCode[i] = window_hash;
        if (hashDict.find(hash) == hashDict.end())
            hashDict.insert({hash, {{i}}});
        else
        {
            auto &lists = hashDict[hash];
            bool notfound = true;
            for (auto &list : lists)
            {
                // check the 0th element of the list only, because the rest of the elements are the same
                if (matches(list[0], i, scan_length))
                {
                    list.push_back(i);
                    notfound = false;
                    break;
                }
            }
            if (notfound)
                // hash collision, the probability of a hash collision in 1787897414 times is about 0.5, solved from e ^ (-n ^ 2 / (2 * (2 ^ 61 - 1))) = 0.5
                // https://en.wikipedia.org/wiki/Birthday_problem
                // create a new list representing a new group of repeating patterns
                lists.push_back({i});
        }

        rolling_hash(window_hash, h, i);
    }

    vector<Matches> matches;
    for (auto &pair : hashDict)
    {
        for (auto &list : pair.second)
        {
            if (list.size() > 1) {
                for (auto &list : disentangle(list)) {
                    // int i = post_condition(list);
                    matches.push_back({scan_length, pair.first, list});
                }
            }
        }
    }
    return matches;
}

void RabinKarp::find_optimal_expansion(const Matches &match, vector<Matches> &optimalCollector) const
{
    for (int i : range(match.indices.size()))
    {
        if (hashDict.find(match.indices[i] + match.scan_length) != hashDict.end()) {
            try_optimal_expansion(match, i, optimalCollector);
            break;
        }
    }
}

void RabinKarp::try_optimal_expansion(const Matches &match, int index, vector<Matches> &optimalCollector) const 
{
    int size = match.indices.size();
    while (index >= 0) {
        int prev_start = match.indices[index];
        int scan_length = match.scan_length;
        int prev_end = prev_start + scan_length;
        Matches newMatch = {scan_length, hashDict.at(prev_end), {prev_start}};
        Matches optimalExpansion = newMatch;
        int indexSkipped = -1;
        for (int i : range(index + 1, size))
        {
            if (prev_end + scan_length >= match.indices[i])
                // no more room to extend, causing collision with the next match
                continue;
            int start = match.indices[i];
            int end = start + scan_length;
            if (hashDict.find(end) != hashDict.end())
            {
                auto hash = hashDict.at(end);
                if (!(newMatch.hashCode == hash && matches(prev_end, end, scan_length)))
                {
                    // record the starting point of the next trial of expansion
                    if (indexSkipped < 0 && hashDict.find(start + scan_length) != hashDict.end())
                        indexSkipped = i;
                }
                else {
                    newMatch.indices.push_back(start);
                    newMatch.hashCode = hash;
                    prev_end = start + scan_length;
                }
            }
        }
        if (newMatch.indices.size() > optimalExpansion.indices.size())
            optimalExpansion = newMatch;
        index = indexSkipped;
        if (optimalExpansion.indices.size() > 1) {
            optimalExpansion.scan_length <<= 1;
            optimalExpansion.hashCode += match.hashCode.shl(scan_length);
            int cmp = optimalCollector.empty()? 0 : optimalExpansion - optimalCollector[0];
            if (cmp > 0)
                optimalCollector.clear();
            else if (cmp < 0)
                continue;
            optimalCollector.push_back(optimalExpansion);
        }
    }
}

vector<Matches> RabinKarp::expand(vector<Matches> &oldMatches) const
{
    vector<Matches> newMatches;
    vector<int> indicesToDelete;
    for (int index : range(oldMatches.size()))
    {
        auto &match = oldMatches[index];
        // if ((std::set<int>{0}).count(match.indices[0]))
            // print("match:", info(match));
        vector<Matches> optimalExpansions;
        find_optimal_expansion(match, optimalExpansions);
        bool extent = true;
        if (!optimalExpansions.empty()) {
            auto &optimalExpansion = optimalExpansions[0];
            extent = optimalExpansion.indices.size() < match.indices.size();
            newMatches.insert(newMatches.end(), optimalExpansions.begin(), optimalExpansions.end());
        }
        if (extent) {
            auto optimalExtension = extend_bytes(match);
            if (optimalExtension.empty())
                optimalExtension = match;
            optimalExtension = extend_byte(optimalExtension);
            if (optimalExtension - match > 0)
                match = optimalExtension;
            else {
                auto new_match = extend_byte(match);
                if (new_match - match > 0)
                    newMatches.push_back(new_match);
            }
        }
        else 
            indicesToDelete.push_back(index);
    }

    del(oldMatches, indicesToDelete);
    return newMatches;
}

double RabinKarp::max_repetition_distance(int scan_length) const {
    return scan_length * pow(2, min(scan_length, 1024) / 12.9) / 2.1 - 10;
}

Matches RabinKarp::extend_bytes(Matches oldMatch) const
{
    int scan_length = oldMatch.scan_length;
    int scan_length_max = scan_length << 1;
    while (scan_length + this->scan_length < scan_length_max)
    {
        int prev_start = oldMatch.indices[0];
        int prev_end = prev_start + scan_length;
        // scan_length might be different from this->scan_length!
        auto prev_hash = hashCode[prev_end];
        int size = oldMatch.indices.size();
        if (size > 1 && prev_end + this->scan_length >= oldMatch.indices[1])
            // no more room to extend, causing collision with the next match
            break; 
        Matches newMatch = {scan_length, prev_hash, {prev_start}};
        Matches optimalExtension = newMatch;
        for (int i : range(1, size)) 
        {
            int prev_end = prev_start + scan_length;
            int start = oldMatch.indices[i];
            int end = start + scan_length;
            auto hash = hashCode[end];
            if (i + 1 < size && end + this->scan_length >= oldMatch.indices[i + 1])
                // no more room to extend, causing collision with the next match
                break; 
            if (!(newMatch.hashCode == hash && matches(prev_end, end, this->scan_length)))
            {
                if (newMatch.indices.size() > optimalExtension.indices.size())
                    optimalExtension = newMatch;
                newMatch.indices.clear();
            }
            newMatch.indices.push_back(start);
            newMatch.hashCode = hash;
            prev_start = start;
        }
        if (newMatch.indices.size() > optimalExtension.indices.size())
            optimalExtension = newMatch;
        if (optimalExtension.empty())
            break;
        scan_length += this->scan_length;
        optimalExtension.scan_length = scan_length;
        optimalExtension.hashCode += oldMatch.hashCode.shl(this->scan_length);
        oldMatch = optimalExtension;
    }
    return oldMatch;
}

Matches RabinKarp::extend_byte(Matches oldMatch) const
{
    int length = text.size();
    int scan_length = oldMatch.scan_length;
    int scan_length_max = scan_length + this->scan_length;
    while (scan_length + 1 < scan_length_max)
    {
        int prev_start = oldMatch.indices[0];
        int prev_end = prev_start + scan_length;
        int size = oldMatch.indices.size();
        if (prev_end >= length || 1 < size && prev_end + 1 >= oldMatch.indices[1])
            // no more room to extend, causing collision with the next match
            break;
        hash_t prev_hash = (unsigned char)text[prev_end];
        Matches newMatch = {scan_length, prev_hash, {prev_start}};
        Matches optimalExtension = newMatch;
        for (int i : range(1, size))
        {
            int start = oldMatch.indices[i];
            int end = start + scan_length;
            if (end >= length || i + 1 < size && end + 1 >= oldMatch.indices[i + 1])
                // no more room to extend, causing collision with the next match
                break;
            hash_t hash = (unsigned char)text[end];
            if (newMatch.hashCode.hash != hash)
            {
                if (newMatch.indices.size() > optimalExtension.indices.size())
                    optimalExtension = newMatch;
                newMatch.indices.clear();
                newMatch.hashCode.hash = hash;
            }
            newMatch.indices.push_back(start);
        }
        if (newMatch.indices.size() > optimalExtension.indices.size())
            optimalExtension = newMatch;
        if (optimalExtension.indices.size() < size)
            break;
        ++scan_length;
        optimalExtension.scan_length = scan_length;
        optimalExtension.hashCode = HashCode(oldMatch.hashCode, optimalExtension.hashCode.hash);
        oldMatch = optimalExtension;
    }
    return oldMatch;
}

void RabinKarp::create_hash_table_for_double_hashing(const vector<Matches> &matches)
{
    hashDict.clear();
    for (auto &match : matches)
    {
        for (int start : match.indices)
        {
            hashDict[start] = match.hashCode;
        }
    }
}

void RabinKarp::debug(const vector<Matches> &matches) const
{
    print("\n\n\nmatches[0].scan_length =", matches[0].scan_length);
    int width = ceil(log10(text.size()));
    for (auto &match : sorted(matches, [](auto &lhs, auto &rhs) { return lhs.indices[0] < rhs.indices[0]; }))
    {
        int scan_length = match.scan_length;
        auto duplicatePattern = text.substr(match.indices[0], scan_length);
        for (int start : match.indices)
        {
            auto end = start + scan_length;
            cout << "text[" << std::setw(width) << start << ":" << std::setw(width) << end << "] = ";
        }
        cout << json_encode(duplicatePattern) << " |>.hash = " << match.hashCode << endl;
    }
    print();
}


void RabinKarp::test()
{
    // Detect redundant patterns in the text
    for (auto &[scan_length, hashCode, indices]: redundancy_detect()) {
        int start = indices[0];
        auto error = text.substr(indices[0], scan_length);
        vector<string> slices;
        for (int start : indices) {
            auto end = start + scan_length;
            slices.push_back("text[" + to_string(start) + ":" + to_string(end) + "]");
        }
        print(
            "length =", scan_length, 
            "count =", indices.size(), 
            join(" = ", slices), "=",
            json_encode(error)
        );
        assert (error.size() == scan_length);
    }
}


vector<Matches> RabinKarp::redundancy_detect()
{
    vector<Matches> result;
    vector<Matches> matches = initial_detect();
    // sort(matches, [](auto &lhs, auto &rhs) { return lhs.indices[0] < rhs.indices[0]; });
    int length = text.size();
    while (!matches.empty() && matches[0].scan_length << 1 <= length)
    {
        create_hash_table_for_double_hashing(matches);
        // debug(matches);
        vector<Matches> newMatches = expand(matches);
        for (auto &match : matches)
        {
            // print("Curr:", info(match));
            vector<int> inferiors;
            bool has_superiors = false;
            for (const auto &[index, m] : enumerate(result))
            {
                if (m.overlap(match))
                {
                    int cmp = m - match;
                    if (cmp < 0)
                        inferiors.push_back(index);
                    else
                    {
                        has_superiors = true;
                        break;
                    }
                }
            }
            if (has_superiors)
                continue;

            if (!inferiors.empty())
                // delete all inferiors;
                del(result, inferiors);

            result.push_back(match);
        }
        matches = newMatches;
    }

    return result;
}

string RabinKarp::substr(const Matches &match) const
{
    if (match.indices.empty())
        return "";
    return text.substr(match.indices[0], match.scan_length);
}

string RabinKarp::info(const Matches &match) const
{
    return json_encode(substr(match)) + " * " + std::to_string(match.indices.size()) + ", with start = " + std::to_string(match.indices[0]) + ", length = " + std::to_string(match.scan_length);
}

int RabinKarp::physic2logic(int physicOffset) const 
{
    return binary_search(this->physicOffset, physicOffset, [](const pair<int, int> &lhs, int rhs) {
        int start = lhs.first;
        int end = lhs.second;
        if (end <= rhs)
            return -1;
        if (start > rhs)
            return 1;
        return 0;
    });
}

void RabinKarp::init_physicOffset(){
    int size = text.size();
    int start = 0;
    while (start < size)
    {
        int end = start + TextC::utf8ByteSize(text[start]);
        physicOffset.push_back({start, end});
        start = end;
    }
}

vector<int> &RabinKarp::physic2logic(vector<int> &indices) const {
    int size = text.size();
    // convert the physic indices to logic indices
    for (auto &index : indices)
        index = this->physic2logic(index);
    return indices;
}