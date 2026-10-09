#include "../keras/layers.h"
#include "NERTagger.h"

using KnapsackNER = NERTagger::KnapsackNER;
using Hit = KnapsackNER::Hit;

KnapsackNER::KnapsackNER(int strlen, const vector<Hit> &partsGiven): Knapsack(strlen, partsGiven, score){
}

float KnapsackNER::score(Hit *hit) {
	return hit->value.score;
}

std::map<String, NERTagger::Value> NERTagger::to_map(const string &vocab) {
	Timer timer(__PRETTY_FUNCTION__);
	std::map<String, NERTagger::Value> treeMap;

	int labelIndex = 0;
	String old = u"\\n";
	String $new = u"\n";
	for (auto &label : labels) {
		for (auto &tuple : Text(vocab + "/" + label + ".txt")) {
			int tabindex = tuple.find_last_of(u'\t');
			auto word = tuple.substr(0, tabindex);
			auto score = tuple.substr(tabindex + 1);
			treeMap[str_replace(old, $new, word)] = {(float)atof(Text::unicode2utf(score).data()), labelIndex};
//			print(word, "=", index);
		}
		++labelIndex;
	}
	return treeMap;
}

NERTagger::NERTagger(const string &vocab) :
		dat(to_map(vocab)) {
}

extern string workingDirectory;
NERTagger& NERTagger::instance_en() {
//	Timer timer(__PRETTY_FUNCTION__);
	static NERTagger inst(workingDirectory + "assets/en/codon/vocab");
	return inst;
}

NERTagger& NERTagger::reinitialize_en() {
//	Timer timer(__PRETTY_FUNCTION__);
	NERTagger &inst = NERTagger::instance_en();
	NERTagger instNew(workingDirectory + "assets/en/codon/vocab");
	inst.dat = instNew.dat;
	return inst;
}

vector<vector<int>> NERTagger::split(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	auto wordList = dat.parseText(text);
	auto partUsed = KnapsackNER(text.size(), wordList).cut();
	vector<vector<int>> result(partUsed.size());
	for (int i : range(result.size())) {
		result[i] = {partUsed[i]->begin, partUsed[i]->end, partUsed[i]->value.label};
	}
	return result;
}

vector<vector<vector<int>>> NERTagger::split(const vector<String> &text) {
	int size = text.size();
	vector<vector<vector<int>>> arr(size);

#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		arr[i] = split(text[i]);
	}
	return arr;
}

vector<vector<vector<vector<int>>>> NERTagger::split(
		const vector<vector<String>> &text) {
	int size = text.size();
	vector<vector<vector<vector<int>>>> arr(size);

#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		arr[i] = split(text[i]);
	}
	return arr;
}

const vector<string> NERTagger::labels = {
	"header", "phrase", "triple", "codon", "field", "number"
};

void NERTagger::test() {
	auto &tagger = NERTagger::instance_en();
	string text = "proteins identified by amino acid\tsequence identity";
	print(text);
	auto result = tagger.split(std::toString(text));
	for (auto &hit : result){
		print(getitem(text, {hit[0], hit[1]}), labels[hit[2]]);
	}
}

extern "C" {

vector<vector<int>> ahocorasick_ner_en(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	return NERTagger::instance_en().split(text);
}

vector<vector<int>> ahocorasick_ner_en_string(const String &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text.size());
	return NERTagger::instance_en().split(text);
}

vector<vector<vector<int>>> ahocorasick_ner_en_batch(const vector<String> &text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	return NERTagger::instance_en().split(text);
}

void ahocorasick_reinitialize_en() {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(text);
	NERTagger::reinitialize_en();
}
}

