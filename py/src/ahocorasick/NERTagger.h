#include "../std/utility.h"
#include "Knapsack.h"


struct NERTagger {

	struct Value {
		float score;
		int label;
	};

	struct KnapsackNER: Knapsack<Value>{
		using Hit = Knapsack::Hit;
		KnapsackNER(int strlen, const vector<Hit> &partsGiven);
		static float score(Hit *);
	};

	vector<vector<int>> split(const String &text);

	vector<vector<vector<int>>> split(const vector<String> &text);

	vector<vector<vector<vector<int>>>> split(const vector<vector<String>> &text);

	NERTagger(const string &vocab);

	AhoCorasickDoubleArrayTrie<char16_t, Value> dat;

	static std::map<String, Value> to_map(const string &vocab);

	static NERTagger& instance_en();
	static NERTagger& reinitialize_en();
	static void test();

	static const vector<string> labels;
};

