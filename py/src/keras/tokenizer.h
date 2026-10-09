#pragma once
#include "../std/utility.h"
#include<vector>
using std::vector;

struct FullTokenizer {
	//Runs end-to-end tokenziation."""

	FullTokenizer(const string &vocab_file, bool do_lower_case = true);
	//    """Runs WordPiece tokenziation."""

	dict<String, int> vocab;
	String unk_token;
	size_t max_input_chars_per_word;
	bool do_lower_case;

	dict<String, int> unknownSet;

	vector<String> basic_tokenize(const String &text);

	vector<String> _run_split_on_punc(String &text);

	bool _is_punctuation(word cp);

	bool _is_chinese_char(word cp);

	String& _clean_text(String &text);

	vector<String> wordpiece_tokenize(String &text);

	vector<String> tokenize(const String &text);

	vector<String> tokenize(const String &text, const String &_text);

	VectorI convert_tokens_to_ids(const vector<String> &items);

	static FullTokenizer& instance_cn();
	static FullTokenizer& instance_en();
};

