#include "../std/utility.h"
#include "AhoCorasickDoubleArrayTrie.h"
#include "Knapsack.h"

struct WordSegmenter {
	struct KnapsackWordSegmenter : Knapsack<float>{
		String text;
		bool output_space_char = false;
		bool split_digits = false;
		using Hit = Knapsack::Hit;
		KnapsackWordSegmenter(const String &text, const vector<Hit> &partsGiven, bool output_space_char=false, bool split_digits=false);

		static float score(Hit *hit);

		void output(vector<String> &outputs, char16_t ch);

		vector<String> convert2segment();

		vector<String> split();
	};

	vector<String> segment(const String &text);
	vector<vector<String>> segment(const vector<String> &text);
	vector<vector<vector<String>>> segment(const vector<vector<String>> &text);

	vector<String> split(const String &text, bool split_digits = false);

	vector<vector<String>> split(const vector<String> &text, bool split_digits = false);

	vector<vector<vector<String>>> split(const vector<vector<String>> &text);

	vector<vector<String>> segment_paralleled(
			const vector<String> &predict_text);

	vector<vector<vector<String>>> segment_paralleled(
			const vector<vector<String>> &predict_text);

	WordSegmenter(const string &vocab);

	AhoCorasickDoubleArrayTrie<char16_t, float> dat;

	void weightAdjustment(const std::map<String, float> &map);

	static std::map<String, float> to_map(const string &vocab);

	static WordSegmenter& instance();

	static WordSegmenter& instance_jp();
};

