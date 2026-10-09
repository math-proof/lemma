#include "public.h"

namespace ahocorasick {

vector<String> loadDictionary(const string &path) {
	vector<String> dictionary;
	for (const auto &s : Text(path)) {
		dictionary.push_back(s);
	}

	return dictionary;
}

vector<String> loadDictionary(const string &path, int limit) {
	vector<String> dictionary;
	Text(path) >> dictionary;
	if (limit)
		return std::sample(dictionary, limit);
	return dictionary;
}

String loadText(const string &path) {
	return Text(path).toString();
}

//int countAhoCorasickDoubleArrayTrie() {
//
//// Build a AhoCorasickDoubleArrayTrie implemented by hankcs
//	AhoCorasickDoubleArrayTrie<String> ahoCorasickDoubleArrayTrie =
//			new AhoCorasickDoubleArrayTrie<String>();
//
//	ahoCorasickDoubleArrayTrie.build(dictionaryMap);
//
//	vector<String> result;
//
//	ahoCorasickDoubleArrayTrie.parseText(text, new AhoCorasickDoubleArrayTrie.IHit<String>() {
//				void hit(int begin, int end, String value) {
////				System.out.printf("%s = %s\n", text.substring(begin, end), value);
//					result.add(value);
//				}
//			});
//	return result.size();
//}

String text;
bool debug = false;
Trie instance;

void initialize(const string &path, int limit) {
	std::map<String, String> dictionaryMap;
	for (String &word : loadDictionary(path, limit)) {
		dictionaryMap[word] = word;
	}

	cout << "dictionary.size() = " << dictionaryMap.size() << endl;
//	text = loadText("text.txt");
//	if (dictionaryMap.size() <= 10) {
//		debug = true;
//	}

	instance.clear();
	instance.dictionaryMap = dictionaryMap;
	instance.build();
}

//#include <algorithm>
//#include <random>
void test() {
	std::map<String, String> dictionaryMap = instance.dictionaryMap;
	vector<String> keywords;
	for (auto &p : dictionaryMap) {
		keywords.push_back(p.first);
	}

	srand(time(NULL));
	std::random_shuffle(keywords.begin(), keywords.end());
//	std::shuffle(keywords.begin(), keywords.end(), std::random_device());

	Trie trieDynamic(dictionaryMap);

	for (auto &wordsToBeDeleted : keywords) {
		cout << "testing word: " << wordsToBeDeleted << endl;

		trieDynamic.erase(wordsToBeDeleted);

		dictionaryMap.erase(wordsToBeDeleted);
		Trie trieConstruct(dictionaryMap);
		dictionaryMap[wordsToBeDeleted] = wordsToBeDeleted;

		assert(
				trieConstruct.parseText(text).size()
						== trieDynamic.parseText(text).size());

		assert(*trieConstruct.rootState == *trieDynamic.rootState);

		trieDynamic.update(wordsToBeDeleted, wordsToBeDeleted);

		assert(
				instance.parseText(text).size()
						== trieDynamic.parseText(text).size());

		assert(*instance.rootState == *trieDynamic.rootState);

	}
}
}
