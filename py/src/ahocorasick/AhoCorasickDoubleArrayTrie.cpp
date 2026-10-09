#include "AhoCorasickDoubleArrayTrie.h"
#include "../keras/utility.h"

void testLoop() {
	const bool debug = true;
	std::map<String, String> dictionaryMap;
	string path = testingDirectory + "ahocorasick/dictionary.txt";

	vector<String> dictionary;

	Text(path) >> dictionary;

//	dictionary.resize(180);
	for (String &word : dictionary) {
		dictionaryMap[word] = u"[" + word + u"]";
	}

	cout << "dictionary.size() = " << dictionaryMap.size() << endl;
	String text =
			Text(testingDirectory + "ahocorasick/dictionary.txt").toString()
					+ Text(testingDirectory + "ahocorasick/text.txt").toString();

	shuffle(dictionary);
	cout << "dictionary.size() = " << dictionary.size() << endl;

//	if (debug) {
//		for (String &word : dictionary) {
//			cout << word << endl;
//		}
//	}

	__timer_begin();
	AhoCorasickDoubleArrayTrie<char16_t, String> dat(dictionaryMap);
	__timer_end();
	cout << "space cost = " << dat.node.size() << endl;

	if (debug) {
//		cout << dat << endl;
	}

	dat.checkValidity();
	vector<AhoCorasickDoubleArrayTrie<char16_t, String>::Hit> arr = dat.parseText(text);

	AhoCorasickDoubleArrayTrie<char16_t, String> _dat(dictionaryMap);

	cout << "space cost = " << _dat.node.size() << endl;

	_dat.checkValidity();
	String debugWord; // = u"水";

	for (String &word : subList(dictionary, 0,
			std::min(100, (int) dictionary.size()))) {
		if (!debugWord.empty() && debugWord != word)
			continue;
//			if (debug)
		cout << "removing word: " << word << endl;

		_dat.remove(word);
		_dat.remove(word);
		if (debug) {
//			cout << _dat << endl;
		}
		_dat.checkValidity();
		_dat.put(word, u"[" + word + u"]");
		_dat.put(word, u"[" + word + u"]");
		if (debug) {
//			cout << _dat << endl;
		}
		_dat.checkValidity();
		assert(dat == _dat);
		vector<AhoCorasickDoubleArrayTrie<char16_t, String>::Hit> _arr = _dat.parseText(
				text);
		assert(arr == _arr);
	}

	cout << "test successfully!" << endl;
}
