#include "../keras/layers.h"
#include "WordSegmenter.h"
#include "Knapsack.h"

using KnapsackWordSegmenter = WordSegmenter::KnapsackWordSegmenter;
using Hit = KnapsackWordSegmenter::Hit;

KnapsackWordSegmenter::KnapsackWordSegmenter(const String &text, const vector<Hit> &partsGiven, bool output_space_char, bool split_digits):
		Knapsack(text.size(), partsGiven, score),
		text(text),
		output_space_char(output_space_char),
		split_digits(split_digits){
	//Timer timer(__PRETTY_FUNCTION__);
}

float KnapsackWordSegmenter::score(Hit *hit){
	return hit->value;
}

vector<String> KnapsackWordSegmenter::split(){
//	Timer timer(__PRETTY_FUNCTION__);
	cut();
	return convert2segment();
}

vector<String> KnapsackWordSegmenter::convert2segment() {
//	Timer timer(__PRETTY_FUNCTION__);
	vector<String> outputs;

	static Hit initial { 0, 0, 0 };
	Hit *prev = &initial;
	for (auto &part : partsUsed) {
		if (prev->end != part->begin) {
			for (int i = prev->end; i < part->begin; ++i) {
				output(outputs, text[i]);
			}
		}

		if (split_digits) {
			String digits = part->substr(text);
			int length = digits.length();
			if (length > 2 && isdigit(digits)) {
				int i = length & 1;
				if (i) {
					outputs.push_back(String(1, digits[0]));
				}

				for (int j = i; j < length; j += 2) {
					outputs.push_back(digits.substr(j, 2));
				}

			} else {
				outputs.push_back(digits);
			}
		} else {
			outputs.push_back(part->substr(text));
		}

		prev = part;
	}

	if (prev->end != (int) text.size()) {
		for (size_t i = prev->end; i < text.size(); ++i) {
			output(outputs, text[i]);
		}
	}

	return outputs;

}

void KnapsackWordSegmenter::output(vector<String> &outputs, char16_t ch) {
	bool isSpaceChar = ::isSpaceChar(ch) || ch == u'\t';
	if (output_space_char) {
		if (!isSpaceChar || outputs.empty())
			outputs.push_back(String(1, ch));
		else {
			outputs.back() += ch;
		}

	} else {
		if (!isSpaceChar)
			outputs.push_back(String(1, ch));
	}
}



std::map<String, float> WordSegmenter::to_map(const string &vocab) {
	std::map<String, float> treeMap;

	for (auto &tuple : Text(vocab).readlines()) {
		int index = tuple.find_last_of(u'\t');
		auto text = tuple.substr(0, index);
		auto value = tuple.substr(index + 1);
		assert(text.size() >= 2);
		treeMap[text] = atof(Text::unicode2utf(value).data());
	}
	return treeMap;
}

WordSegmenter::WordSegmenter(const string &vocab) :
		dat(to_map(vocab)) {
}

void WordSegmenter::weightAdjustment(const std::map<String, float> &map) {
	for (auto &entry : map) {
		auto &text = entry.first;
		auto array = dat.parseTextIndexed(text);
		if (array.size() > 1) {
			auto last = array.back();
			array.pop_back();

			float score = last.value;
			for (auto &hit : array) {
				if (hit.value >= score) {
					score = hit.value + 0.01;
				}
			}
			if (score != last.value) {
				last.setValue(score);
			}
		}
	}

	dat.root = nullptr;
}

extern string workingDirectory;
WordSegmenter& WordSegmenter::instance() {
//	print(__PRETTY_FUNCTION__)
	static WordSegmenter inst(workingDirectory + "assets/cn/segment/vocab.csv");
	return inst;
}

WordSegmenter& WordSegmenter::instance_jp() {
//	print(__PRETTY_FUNCTION__)
	static WordSegmenter inst(workingDirectory + "assets/jp/segment/vocab.csv");
	return inst;
}

vector<String> WordSegmenter::segment(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	return KnapsackWordSegmenter(text, dat.parseText(text)).split();
}

vector<String> WordSegmenter::split(const String &text, bool split_digits) {
	const auto &wordList = dat.parseText(text);
	auto knapsack = KnapsackWordSegmenter(text, wordList, true, split_digits);
	knapsack.cut();
	return knapsack.convert2segment();
}

vector<vector<String>> WordSegmenter::split(const vector<String> &text,
		bool split_digits) {
	int size = text.size();
	vector<vector<String>> arr(size);

#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		arr[i] = split(text[i], split_digits);
	}
	return arr;
}

vector<vector<vector<String>>> WordSegmenter::split(
		const vector<vector<String>> &text) {
	int size = text.size();
	vector<vector<vector<String>>> arr(size);

#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		arr[i] = split(text[i]);
	}
	return arr;
}

vector<vector<String>> WordSegmenter::segment(const vector<String> &text) {
	int size = text.size();
	vector<vector<String>> arr(size);
	for (int i = 0; i < size; ++i) {
		arr[i] = segment(text[i]);
	}

	return arr;
}

vector<vector<vector<String>>> WordSegmenter::segment(
		const vector<vector<String>> &text) {
	int size = text.size();
	vector<vector<vector<String>> > arr(size);
	for (int i = 0; i < size; ++i) {
		arr[i] = segment(text[i]);
	}

	return arr;
}

extern "C" {

vector<String> ahocorasick_cws_segment(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	return WordSegmenter::instance().segment(text);
}

vector<String> ahocorasick_cws_split(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto result = WordSegmenter::instance().split(text);
	return result;
}

vector<String> ahocorasick_cws_split_digits(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	return WordSegmenter::instance().split(text, true);
}

vector<vector<String>> ahocorasick_cws_split_s(const vector<String> &text) {
	return WordSegmenter::instance().split(text);
}

vector<vector<String>> ahocorasick_cws_split_s_digits(
		const vector<String> &text) {
	return WordSegmenter::instance().split(text, true);
}

vector<vector<vector<String>>> ahocorasick_jws_split_ss(
		const vector<vector<String>> &text) {
	return WordSegmenter::instance_jp().split(text);
}

vector<String> ahocorasick_jws_split(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	auto result = WordSegmenter::instance_jp().split(text);
//	print(result);
	return result;
}

vector<String> ahocorasick_jws_split_digits(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	auto result = WordSegmenter::instance_jp().split(text, true);
//	print(result);
	return result;
}

vector<vector<String>> ahocorasick_jws_split_s(const vector<String> &text) {
	return WordSegmenter::instance_jp().split(text);
}

vector<vector<String>> ahocorasick_jws_split_s_digits(
		const vector<String> &text) {
	return WordSegmenter::instance_jp().split(text, true);
}
}

