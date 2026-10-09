#include "bert.h"
#include "matrix.h"
#include "../std/lagacy.h"
#include "utility.h"

vector<String> whitespace_tokenize(String &text) {
//        """Runs basic whitespace cleaning and splitting on a piece of text."""
	text = strip(text);
	if (!text)
		return vector<String>();
	return split(text);
}

FullTokenizer::FullTokenizer(const string &vocab_file, bool do_lower_case) :
		vocab(Text(vocab_file).read_vocab(0)), unk_token(u"[UNK]"),
		max_input_chars_per_word(200), do_lower_case(do_lower_case) {
			Timer timer(__PRETTY_FUNCTION__);
		}

FullTokenizer& FullTokenizer::instance_cn() {
	static FullTokenizer instance(assetsDirectory() + "cn/bert/vocab.txt");
	return instance;
}

FullTokenizer& FullTokenizer::instance_en() {
	static FullTokenizer instance(
			assetsDirectory() + "en/bert/albert_base/vocab.txt");
	return instance;
}

VectorI FullTokenizer::convert_tokens_to_ids(const vector<String> &items) {
	VectorI output(items.size());

	int index = 0;
	for (auto &item : items) {
		auto iter = vocab.find(item);
//		output(index) = iter == vocab.end() ? -vocab.at(lstrip(item)) : iter->second;
		output[index] = iter == vocab.end() ? 1 : iter->second;

		++index;
	}
	return output;
}

vector<String> FullTokenizer::wordpiece_tokenize(String &chars) {
//        """Tokenizes a piece of text into its word pieces.
//
//        This uses a greedy longest-match-first algorithm to perform tokenization
//        using the given vocabulary.
//
//        For example:
//            input = "unaffable"
//            output = ["un", "##aff", "##able"]
//
//        Args:
//            text: A single token or whitespace separated tokens. This should have
//                already been passed through `FullTokenizer.
//
//        Returns:
//            A list of wordpiece tokens.
//        """

	vector<String> output_tokens;

	if (chars.size() > max_input_chars_per_word) {
		output_tokens.push_back(unk_token);
	} else {
		if (do_lower_case)
			tolower(chars);

		bool is_bad = false;
		size_t start = 0;

		while (start < chars.size()) {
			auto end = chars.size();
			String cur_substr, substr;
			while (start < end) {
				substr = chars.substr(start, end - start);
				if (start > 0) {
					substr = u"##" + substr;
				}

				if (vocab.count(substr)) {
					cur_substr = substr;
					break;
				}
				--end;
			}
			if (!cur_substr) {
				is_bad = true;
				if (unknownSet.count(substr)) {
					unknownSet[substr] += 1;
				} else {
					cout << "unknown word encountered " << substr << ", from "
							<< chars << endl;
					unknownSet[substr] = 1;
				}
				break;
			}

			output_tokens.push_back(cur_substr);
			start = end;
		}

		if (is_bad)
			output_tokens.push_back(unk_token);
	}

	chars.clear();
	return output_tokens;
}

vector<String> FullTokenizer::_run_split_on_punc(String &text) {
//        """Splits punctuation on a piece of text."""
	size_t i = 0;
	bool start_new_word = true;
	vector<String> output;

	while (i < text.size()) {
		auto ch = text[i];
		if (_is_punctuation(ch)) {
			output <<= { String(1, ch) };
			start_new_word = true;
		} else {
			if (start_new_word)
				output <<= { u""};

			start_new_word = false;
			output.back() += ch;
		}
		++i;
	}

	return output;
}

vector<String> FullTokenizer::tokenize(const String &x, const String &y) {
	vector<String> s;
	s <<= { u"[CLS]"};
	s << tokenize(x);
	s <<= { u"[SEP]"};
	s << tokenize(y);
	s <<= { u"[SEP]"};
	return s;
}

vector<String> FullTokenizer::tokenize(const String &text) {
//# This was added on November 1st, 2018 for the multilingual and Chinese
//# models. This is also applied to the English models now, but it doesn't
//# matter since the English models were not trained on any Chinese data
//# and generally don't have any Chinese data in them (there are Chinese
//# characters in the vocabulary because Wikipedia does have some Chinese
//# words in the English Wikipedia.).

//        """Adds whitespace around any CJK character."""
//cout << "text = " << text << endl;
//	Timer timer(__PRETTY_FUNCTION__);
	vector<String> output;
	String word;

	for (auto ch : text) {
		if (ch == 0 || ch == 0xfffd || iswcntrl(ch)) {
			continue;
		}

		if (isspace(ch)) {
			if (!!word) {
				//	cout << "word = " << word << endl;
				output << wordpiece_tokenize(word);
			}
			continue;
		}

		if (_is_chinese_char(ch) || _is_punctuation(ch)) {
			if (!!word) {
				//		cout << "word = " << word << endl;
				output << wordpiece_tokenize(word);
			}

			String substr(1, ch);
			if (vocab.count(substr))
				output.push_back(substr);
			else
				output.push_back(this->unk_token);
		} else {
			word += ch;
		}
	}

	if (!!word) {
//		print(word);
		output << wordpiece_tokenize(word);
	}
//	print(output);

	return output;
}

bool FullTokenizer::_is_punctuation(word cp) {
//        """Checks whether `chars` is a punctuation character."""
//    # We treat all non-letter/number ASCII as punctuation.
//    # Characters such as "^", "$", and "`" are not in the Unicode
//    # Punctuation class but we treat them as punctuation anyways, for
//    # consistency.
	if ((cp >= 33 && cp <= 47) || (cp >= 58 && cp <= 64)
			|| (cp >= 91 && cp <= 96) || (cp >= 123 && cp <= 126))
		return true;
	return iswpunct(cp);
}

bool FullTokenizer::_is_chinese_char(word cp) {
//        """Checks whether CP is the codepoint of a CJK character."""
//# This defines a "chinese character" as anything in the CJK Unicode block:
//#   https://en.wikipedia.org/wiki/CJK_Unified_Ideographs_(Unicode_block)
//#
//# Note that the CJK Unicode block is NOT all Japanese and Korean characters,
//# despite its name. The modern Korean Hangul alphabet is a different block,
//# as is Japanese Hiragana and Katakana. Those alphabets are used to write
//# space-separated words, so they are not treated specially and handled
//# like the all of the other languages.
	if ((cp >= 0x4E00 && cp <= 0x9FFF) || (cp >= 0x3400 && cp <= 0x4DBF) ||
//            (cp >= 0x20000 && cp <= 0x2A6DF) ||
//            (cp >= 0x2A700 && cp <= 0x2B73F) ||
//            (cp >= 0x2B740 && cp <= 0x2B81F) ||
//            (cp >= 0x2B820 && cp <= 0x2CEAF) ||
			(cp >= 0xF900 && cp <= 0xFAFF) //||
//            (cp >= 0x2F800 && cp <= 0x2FA1F))
			)
		return true;

	return false;
}

String& FullTokenizer::_clean_text(String &text) {
//        """Performs invalid character removal and whitespace cleanup on text."""
	for (size_t i = 0; i < text.size();) {
		word ch = text[i];
		if (ch == 0 || ch == 0xfffd || iswcntrl(ch)) {
			text.erase(i);
			continue;
		}

		if (isspace(ch)) {
			text[i] = ' ';
		}
		++i;
	}
	return text;
}

extern "C" {
vector<String> keras_tokenizer_en(String &text) {
	Timer timer(__PRETTY_FUNCTION__);
	auto tokens = FullTokenizer::instance_en().tokenize(text);
	print(tokens);
	return tokens;
}

}
