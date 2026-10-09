#include "../std/utility.h"
#include <map>

#include "Trie.h"

namespace ahocorasick {
extern String text;
extern bool debug;
extern Trie instance;

vector<String> loadDictionary(const string &path =
		"../corpus/ahocorasick/en/dictionary.txt");

vector<String> loadDictionary(const string&, int limit);

String loadText(const string &path = "../corpus/ahocorasick/en/text.txt");

int countAhoCorasickDoubleArrayTrie();
void initialize(const string &path, int limit = 0);
void test();
}
