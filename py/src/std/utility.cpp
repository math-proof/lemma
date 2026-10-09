#include "utility.h"
#include <string>

void print()
{
	std::cout << std::endl;
}

// to include strlen
#include <cstring>

size_t TextC::utf8ByteSize(unsigned char first_byte)
{
	// for error: return 0
	// for valid results: return 1-6

	// UTF8 encoding format：
	// closed integer interval : 0        1        2        3        4        5
	// [U-00000000, U-0000007F]: 0xxxxxxx
	// [U-00000080, U-000007FF]: 110xxxxx 10xxxxxx
	// [U-00000800, U-0000FFFF]: 1110xxxx 10xxxxxx 10xxxxxx
	// [U-00010000, U-001FFFFF]: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
	// [U-00200000, U-03FFFFFF]: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
	// [U-04000000, U-7FFFFFFF]: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx

	// 1-byte 0xxxxxxx
	if (first_byte < 0b10000000)
		return 1;
	// 2-byte 110xxxxx
	if ((first_byte & 0b11100000) == 0b11000000)
		return 2;
	// 3-byte 1110xxxx: First byte masked with 0xF0 equals 0xE0.
	if ((first_byte & 0b11110000) == 0b11100000)
		return 3;
	// 4-byte 11110xxx
	if ((first_byte & 0b11111000) == 0b11110000)
		return 4;
	// 5-byte 111110xx
	if ((first_byte & 0b11111100) == 0b11111000) // 5-byte (invalid)
		return 5;
	// 6-byte 1111110x
	if ((first_byte & 0b11111110) == 0b11111100) // 6-byte (invalid)
		return 6;
	return 0; // Other invalid patterns (e.g., continuation bytes)
}

char TextC::get_bits(char ch, int start, int size, int shift)
{
	return ((ch >> start) & ((1 << size) - 1)) << shift;
}

char TextC::get_bits(char ch, int start, int size, char _ch)
{
	return get_bits(ch, start, size, _ch, 8 - size);
}

char TextC::get_bits(char ch, int start, int size, char _ch, int _size)
{
	return get_bits(_ch, 0, _size, size) + get_bits(ch, start, size);
}

string Text::unicode2utf(const String &wstr)
{
	string s;
	//	s.clear();
	char str[7];
	for (word wc : wstr)
	{
		s += unicode2utf((int)wc, str);
	}
	return s;
}

void Text::test_utf_unicode_conversion()
{
	char str[7];
	for (word wc = 1; wc > 0; ++wc)
	{
		auto cstr = unicode2utf((int)wc, str);
		auto _wc = utf2unicode(cstr, strlen(cstr));
		assert(_wc == wc);
		if (_wc != wc)
		{
			cout << wc << " != " << _wc << endl;
		}
		else
		{
			//			cout << wc << " == " << _wc << endl;
		}
	}
}

int Text::surrogate_pairs(int nonBMP)
{
	// `nonBMP` represents a Unicode character beyond the Basic Multilingual Plane
	int res_jchars = 0xdc00d800;
	auto jchars = (word *)&res_jchars;
	//	jchars[0] = 0xd800;
	//	jchars[1] = 0xdc00;

	nonBMP -= 65536;

	jchars[0] |= nonBMP >> 10;
	jchars[1] |= nonBMP & 0x03ff;
	// (word *)&res_jchars represent the surrogate_pairs of utf-16 encoding that occurs in java/javascript
	return res_jchars;
}

uint32_t Text::surrogate_pairs_s(uint32_t unicode)
{
    unicode -= 0x10000; // Normalize to 20-bit plane
    uint16_t high = 0xD800 | (unicode >> 10);  // High surrogate
    uint16_t low  = 0xDC00 | (unicode & 0x3FF); // Low surrogate
    return (static_cast<uint32_t>(high) << 16) | low; // Pack both into 32-bit
}

int Text::utf2unicode(const char *pText, int length)
{
	//	https://blog.csdn.net/qq_38279908/article/details/89329740
	//	https://www.cnblogs.com/cfas/p/7931787.html
	//  #include <codecvt>        // std::codecvt_utf8
	//	return std::wstring_convert<std::codecvt_utf8<wchar_t> >().from_bytes(str);
	int wc = 0;
	char *uchar = (char *)&wc;

	//	if (length == 0) {
	//		length = strlen(pText);
	//	}

	switch (length)
	{
	case 1:
		uchar[1] = 0;
		uchar[0] = pText[0];
		break;
	case 2:
		//		U-000007FF: 110xxxxx 10xxxxxx
		uchar[1] = TextC::get_bits(pText[0], 2, 4);
		uchar[0] = TextC::get_bits(pText[1], 0, 6, pText[0]);
		break;
	case 3:
		//		U-0000FFFF: 1110xxxx 10xxxxxx 10xxxxxx
		uchar[1] = TextC::get_bits(pText[1], 2, 4, pText[0]);
		uchar[0] = TextC::get_bits(pText[2], 0, 6, pText[1]);
		break;
	case 4:
		//		U-001FFFFF: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
		uchar[2] = TextC::get_bits(pText[1], 4, 2, pText[0], 4);
		uchar[1] = TextC::get_bits(pText[2], 2, 4, pText[1]);
		uchar[0] = TextC::get_bits(pText[3], 0, 6, pText[2]);
		break;
	case 5:
		//		U-03FFFFFF: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
		uchar[3] = TextC::get_bits(pText[0], 0, 3);
		uchar[2] = TextC::get_bits(pText[2], 4, 2, pText[1]);
		uchar[1] = TextC::get_bits(pText[3], 2, 4, pText[2]);
		uchar[0] = TextC::get_bits(pText[4], 0, 6, pText[3]);
		break;
	case 6:
		//		U-7FFFFFFF: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
		uchar[3] = TextC::get_bits(pText[1], 0, 6, pText[0]);
		uchar[2] = TextC::get_bits(pText[3], 4, 2, pText[2]);
		uchar[1] = TextC::get_bits(pText[4], 2, 4, pText[3]);
		uchar[0] = TextC::get_bits(pText[5], 0, 6, pText[4]);
		break;
	default:;
	}
	return wc;
}

const char *Text::unicode2utf(int wc, char *pText)
{
	//	https://blog.csdn.net/qq_38279908/article/details/89329740
	//	https://www.cnblogs.com/cfas/p/7931787.html
	//	return std::wstring_convert<std::codecvt_utf8<wchar_t> >().to_bytes(wstr);
	//	static char str[7];
	//	if (!pText) {
	//		pText = str;
	//	}

	char *uchar = (char *)&wc;

	if (!(wc & ~0x0000007F))
	{
		//      U-00000000 - U-0000007F: 0xxxxxxx
		pText[0] = uchar[0];
		pText[1] = 0;
	}
	else if (!(wc & ~0x000007FF))
	{
		//		U-00000080 - U-000007FF: 110xxxxx 10xxxxxx
		pText[0] = 0xC0 + TextC::get_bits(uchar[1], 0, 4, 2) + TextC::get_bits(uchar[0], 6, 2);
		pText[1] = 0x80 + TextC::get_bits(uchar[0], 0, 6);
		pText[2] = 0;
	}
	else if (!(wc & ~0x0000FFFF))
	{
		//		U-00000800 - U-0000FFFF: 1110xxxx 10xxxxxx 10xxxxxx
		pText[0] = 0xE0 + TextC::get_bits(uchar[1], 4, 4);
		pText[1] = 0x80 + TextC::get_bits(uchar[1], 0, 4, 2) + TextC::get_bits(uchar[0], 6, 2);
		pText[2] = 0x80 + TextC::get_bits(uchar[0], 0, 6);
		pText[3] = 0;
	}
	else if (!(wc & ~0x001FFFFF))
	{
		//		U-00010000 - U-001FFFFF: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
		pText[0] = 0xF0 + TextC::get_bits(uchar[2], 5, 3);
		pText[1] = 0x80 + TextC::get_bits(uchar[2], 0, 2, 4) + TextC::get_bits(uchar[1], 4, 4);
		pText[2] = 0x80 + TextC::get_bits(uchar[1], 0, 4, 2) + TextC::get_bits(uchar[0], 6, 2);
		pText[3] = 0x80 + TextC::get_bits(uchar[0], 0, 6);
		pText[4] = 0;
	}
	else if (!(wc & ~0x03FFFFFF))
	{
		//		U-00200000 - U-03FFFFFF: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
		pText[0] = 0xF8 + TextC::get_bits(uchar[3], 0, 2);
		pText[1] = 0x80 + TextC::get_bits(uchar[2], 2, 6);
		pText[2] = 0x80 + TextC::get_bits(uchar[2], 0, 2, 4) + TextC::get_bits(uchar[1], 4, 4);
		pText[3] = 0x80 + TextC::get_bits(uchar[1], 0, 4, 2) + TextC::get_bits(uchar[0], 6, 2);
		pText[4] = 0x80 + TextC::get_bits(uchar[0], 0, 6);
		pText[5] = 0;
	}
	else
	{
		//		U-04000000 - U-7FFFFFFF: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
		pText[0] = 0xFC + TextC::get_bits(uchar[3], 7, 1);
		pText[1] = 0x80 + TextC::get_bits(uchar[3], 0, 6);
		pText[2] = 0x80 + TextC::get_bits(uchar[2], 2, 6);
		pText[3] = 0x80 + TextC::get_bits(uchar[2], 0, 2, 4) + TextC::get_bits(uchar[1], 4, 4);
		pText[4] = 0x80 + TextC::get_bits(uchar[1], 0, 4, 2) + TextC::get_bits(uchar[0], 6, 2);
		pText[5] = 0x80 + TextC::get_bits(uchar[0], 0, 6);
		pText[6] = 0;
	}

	return pText;
}

Text::operator bool()
{
	if (file)
		return true;
	return false;
	//	return file.operator bool();
}

TextC::operator bool()
{
	if (file)
		return true;
	return false;
}

Text::Text(const string &file) : file(file.c_str())
{
	print(file);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
	int wc;
	if (*this >> wc)
	{
		if (wc != 0xfeff)
		{
			this->file.seekg(0, std::ios::beg);
		}
#pragma GCC diagnostic pop
	}
}

TextC::TextC(const string &file) : file(file.c_str())
{
	print(file);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
	int wc;
	if (*this >> wc)
	{
		if (wc != 0xfeff)
		{
			this->file.seekg(0, std::ios::beg);
		}
#pragma GCC diagnostic pop
	}
}

Text::iterator::iterator(Text *text, bool eof) : text(text), eof(eof)
{
}

TextC::iterator::iterator(TextC *text, bool eof) : text(text), eof(eof)
{
}

bool Text::iterator::operator!=(iterator &end)
{
	return this->eof != end.eof;
}

bool TextC::iterator::operator!=(iterator &end)
{
	return this->eof != end.eof;
}

Text::iterator &Text::iterator::operator++()
{
	if (*text >> text->line)
	{
		eof = false;
	}
	else
	{
		eof = text->line.empty();
	}

	return *this;
}

TextC::iterator &TextC::iterator::operator++()
{
	if (*text >> text->line)
	{
		eof = false;
	}
	else
	{
		eof = text->line.empty();
	}

	return *this;
}

String &Text::iterator::operator*()
{
	return text->line;
}

string &TextC::iterator::operator*()
{
	return text->line;
}

Text::iterator Text::begin()
{
	bool eof;
	if (*this >> line)
	{
		eof = false;
	}
	else
	{
		eof = true;
	}

	return iterator(this, eof);
}

Text::iterator Text::end()
{
	return iterator(this, true);
}

TextC::iterator TextC::begin()
{
	bool eof;
	if (*this >> line)
	{
		eof = false;
	}
	else
	{
		eof = true;
	}

	return iterator(this, eof);
}

TextC::iterator TextC::end()
{
	return iterator(this, true);
}

Text &Text::operator>>(int &unicode)
{
	char str[6];
	if (file.get(str[0]))
	{
		int length = TextC::utf8ByteSize(str[0]);
		file.read(str + 1, length - 1);
		unicode = utf2unicode(str, length);
	}
	return *this;
}

String Text::toString()
{
	vector<String> v;
	*this >> v;
	String tmp;
	for (auto &s : v)
		tmp += s;
	return tmp;
}

string TextC::read() const {
	std::ostringstream ss;
	ss << file.rdbuf();
	return ss.str();
}

string TextC::toString()
{
	vector<string> v;
	*this >> v;
	string tmp;
	for (auto &s : v)
		tmp += s;
	return tmp;
}

vector<String> Text::readlines()
{
	vector<String> v;
	*this >> v;
	return v;
}

vector<string> TextC::readlines()
{
	vector<string> v;
	*this >> v;
	return v;
}

Text &Text::operator>>(vector<String> &v)
{
	String line;
	if (v.size())
	{
		for (size_t i = 0; i < v.size(); ++i)
		{
			if (*this >> line)
				v[i] = line;
			else
			{
				if (!line.empty())
					v[i] = line;
				break;
			}
		}
	}
	else
	{
		while (*this >> line)
		{
			v.push_back(line);
		}

		if (!line.empty())
			v.push_back(line);
	}
	return *this;
}

TextC &TextC::operator>>(vector<string> &v)
{
	string line;
	if (v.size())
	{
		for (size_t i = 0; i < v.size(); ++i)
		{
			if (*this >> line)
				v[i] = line;
			else
			{
				if (!line.empty())
					v[i] = line;
				break;
			}
		}
	}
	else
	{
		while (*this >> line)
		{
			v.push_back(line);
		}

		if (!line.empty())
			v.push_back(line);
	}
	return *this;
}

String &Text::append_unicode(String &v, int wc)
{
	if (wc & 0xffff0000)
	{
		wc = surrogate_pairs(wc);
		auto jchars = (word *)&wc;
		v += jchars[0];
		v += jchars[1];
	}
	else
		v += wc;
	return v;
}

Text &Text::operator>>(String &v)
{
	v.clear();
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
	int wc;

	while (*this >> wc)
	{
		if (wc == '\r' || wc == '\n')
		{
			if (v.size())
				break;
			else
				continue;
		}
		append_unicode(v, wc);
	}
#pragma GCC diagnostic pop
	return *this;
}

TextC &TextC::operator>>(string &v)
{
	std::getline(file, v);
	return *this;
}

dict<String, int> Text::read_vocab(int index)
{
	Timer timer(__PRETTY_FUNCTION__);
	dict<String, int> word2id;
	return read_vocab(word2id, index);
}

dict<string, int> Text::read_vocab_cstr()
{
	dict<string, int> word2id;
	//	Timer timer(__PRETTY_FUNCTION__);
	string s;
	int index = 0;
	while (std::getline(file, s))
	{
		strip(s);
		s = s.substr(0, s.find_first_of('\t'));
		assert(!s.empty());

		assert(word2id.count(s) == 0);

		word2id[s] = index++;
	}
	cout << "word2id.size() = " << word2id.size() << endl;
	cout << "index = " << index << endl;
	return word2id;
}

dict<String, int> &Text::read_vocab(dict<String, int> &word2id, int index)
{
	Timer timer(__PRETTY_FUNCTION__);
	word2id.clear();
	String s;
	for (String &s : *this)
	{
		strip(s);
		//		print(s);
		assert(!s.empty());
		//		cout << s << " = " << index << endl;
		//		cout << "s.size() = " << s.size() << endl;
		assert(word2id.count(s) == 0);

		word2id[s] = index++;
	}
	cout << "word2id.size() = " << word2id.size() << endl;
	cout << "index = " << index << endl;
	return word2id;
}

dict<string, int> &Text::read_vocab(dict<string, int> &word2id, int index)
{
	Timer timer(__PRETTY_FUNCTION__);
	word2id.clear();
	string s;
	while (std::getline(file, s))
	{
		strip(s);
		assert(!s.empty());

		assert(word2id.count(s) == 0);

		word2id[s] = index++;
	}
	cout << "word2id.size() = " << word2id.size() << endl;
	cout << "index = " << index << endl;
	return word2id;
}

dict<char16_t, int> Text::read_vocab_char()
{
	dict<char16_t, int> word2id;
	*this >> word2id;
	return word2id;
}

Text &Text::operator>>(dict<String, int> &word2id)
{
	this->read_vocab(word2id, 2);
	return *this;
}

Text &Text::operator>>(dict<char16_t, int> &word2id)
{
	word2id.clear();
	String s;
	size_t index = 2;
	for (String &s : *this)
	{
		strip(s);
		assert(s.size() == 1);
		char16_t ch = s[0];
		//		cout << s << " = " << index << endl;
		//		cout << "s.size() = " << s.size() << endl;
		assert(word2id.count(ch) == 0);

		word2id[ch] = index++;
	}
	cout << "word2id.size() = " << word2id.size() << endl;
	cout << "index = " << index << endl;
	assert(word2id.size() == index - 2);
	return *this;
}

#include <fstream>
using namespace std;

#if defined(_DEBUG) or defined(__WIN64__)
#include <windows.h>
string Text::unicode2gbk(const String &wstr)
{
	string result;
	static_assert(sizeof(wchar_t) == sizeof(char16_t));
	int n = WideCharToMultiByte(CP_ACP, 0, (const wchar_t *)wstr.c_str(), -1, 0,
								0, 0, 0);
	result.resize(n - 1);
	::WideCharToMultiByte(CP_ACP, 0, (const wchar_t *)wstr.c_str(), -1,
						  (char *)result.c_str(), n, 0, 0);
	return result;
}
#endif

std::ostream &operator<<(std::ostream &cout, const String &unicode)
{
#if defined(_DEBUG) // or defined(__WIN64__)
	cout << Text::unicode2gbk(unicode);
#else
	cout << Text::unicode2utf(unicode);
#endif

	return cout;
}

std::ostream &operator<<(std::ostream &cout, const bytes &str)
{
	cout << (const char *)str.c_str();
	return cout;
}

String operator+(const String &lhs, int rhs)
{
	return lhs + toString(rhs);
}

vector<String> split(const String &in)
{
	vector<String> array;
	String s;
	for (auto ch : in)
	{
		if (isspace(ch))
		{
			if (!s.empty())
			{
				array.push_back(s);
				s.clear();
			}
		}
		else
		{
			s += ch;
		}
	}

	if (!s.empty())
	{
		array.push_back(s);
	}
	return array;
}

vector<string> split(const string &in)
{
	vector<string> array;
	string s;
	for (auto ch : in)
	{
		if (isspace(ch))
		{
			if (!s.empty())
			{
				array.push_back(s);
				s.clear();
			}
		}
		else
		{
			s += ch;
		}
	}

	if (!s.empty())
	{
		array.push_back(s);
	}
	return array;
}

vector<string> split(const string &in, char separator)
{
	vector<string> array;
	string s;
	for (auto ch : in)
	{
		if (ch == separator)
		{
			if (!s.empty())
			{
				array.push_back(s);
				s.clear();
			}
		}
		else
		{
			s += ch;
		}
	}

	if (!s.empty())
	{
		array.push_back(s);
	}
	return array;
}

namespace std
{
	int strlen(const String &value)
	{
		int length = 0;
		for (auto ch : value)
		{
			if ((ch & 0xff80) != 0)
				length += 2;
			else
				++length;
		}
		return length;
	}

	int strlen(const string &value)
	{
		return value.size();
	}

#include <sstream>
	String toString(int d)
	{
		return toString(std::to_string(d));
	}

	vector<String> toStrings(const vector<string> &c_str)
	{
		int size = c_str.size();
		vector<String> texts(size);

		for (int i = 0; i < size; ++i)
		{
			texts[i] = toString(c_str[i]);
		}
		return texts;
	}

	vector<vector<String>> toStrings(const vector<vector<string>> &c_str)
	{
		int size = c_str.size();
		vector<vector<String>> texts(size);

		for (int i = 0; i < size; ++i)
		{
			texts[i] = toStrings(c_str[i]);
		}
		return texts;
	}

	String toString(const char *c_str, int size)
	{
		String s;
		for (size_t j = 0; j < size;)
		{
			auto &ch = c_str[j];
			auto length = TextC::utf8ByteSize(ch);
			if (length == 0)
				return u"??";

			j += length;

			ensure_le(j, size);

			Text::append_unicode(s, Text::utf2unicode(&ch, length));
		}

		return s;
	}

	String toString(const char *c_str)
	{
		return toString(c_str, strlen(c_str));
	}

	String toString(const string &c_str)
	{
		return toString(c_str.c_str(), c_str.size());
	}
	// possible bugs
	string to_string(const String &wstr)
	{
		string s;
		char str[7];
		for (word wc : wstr)
		{
			s += Text::unicode2utf((int)wc, str);
		}
		return s;
	}

}

#pragma GCC diagnostic ignored "-Wparentheses"
//	[a-zA-Zａ-ｚＡ-Ｚα-ϋΑ-Ϋа-яА-Яⅰ-ⅿⅠ-Ⅿ]
//	[a-zａ-ｚα-ϋа-яⅰ-ⅿ]
//	[A-ZＡ-ＺΑ-ΫА-ЯⅠ-Ⅿ]
char16_t tolower(char16_t ch)
{
	switch (ch)
	{
		// English big letters:
	case u'A':
	case u'B':
	case u'C':
	case u'D':
	case u'E':
	case u'F':
	case u'G':
	case u'H':
	case u'I':
	case u'J':
	case u'K':
	case u'L':
	case u'M':
	case u'N':
	case u'O':
	case u'P':
	case u'Q':
	case u'R':
	case u'S':
	case u'T':
	case u'U':
	case u'V':
	case u'W':
	case u'X':
	case u'Y':
	case u'Z':
		// English wide big letters:
	case u'Ａ':
	case u'Ｂ':
	case u'Ｃ':
	case u'Ｄ':
	case u'Ｅ':
	case u'Ｆ':
	case u'Ｇ':
	case u'Ｈ':
	case u'Ｉ':
	case u'Ｊ':
	case u'Ｋ':
	case u'Ｌ':
	case u'Ｍ':
	case u'Ｎ':
	case u'Ｏ':
	case u'Ｐ':
	case u'Ｑ':
	case u'Ｒ':
	case u'Ｓ':
	case u'Ｔ':
	case u'Ｕ':
	case u'Ｖ':
	case u'Ｗ':
	case u'Ｘ':
	case u'Ｙ':
	case u'Ｚ':
		// Greek big letters:
	case u'Α':
	case u'Β':
	case u'Γ':
	case u'Δ':
	case u'Ε':
	case u'Ζ':
	case u'Η':
	case u'Θ':
	case u'Ι':
	case u'Κ':
	case u'Λ':
	case u'Μ':
	case u'Ν':
	case u'Ξ':
	case u'Ο':
	case u'Π':
	case u'Ρ':
	case u'Σ':
	case u'Τ':
	case u'Υ':
	case u'Φ':
	case u'Χ':
	case u'Ψ':
	case u'Ω':
	case u'Ϊ':
	case u'Ϋ':
		// Russian big letters:
	case u'А':
	case u'Б':
	case u'В':
	case u'Г':
	case u'Д':
	case u'Е':
	case u'Ж':
	case u'З':
	case u'И':
	case u'Й':
	case u'К':
	case u'Л':
	case u'М':
	case u'Н':
	case u'О':
	case u'П':
	case u'Р':
	case u'С':
	case u'Т':
	case u'У':
	case u'Ф':
	case u'Х':
	case u'Ц':
	case u'Ч':
	case u'Ш':
	case u'Щ':
	case u'Ъ':
	case u'Ы':
	case u'Ь':
	case u'Э':
	case u'Ю':
	case u'Я':
		return ch + 32;
		// Roman big digits
	case u'Ⅰ':
	case u'Ⅱ':
	case u'Ⅲ':
	case u'Ⅳ':
	case u'Ⅴ':
	case u'Ⅵ':
	case u'Ⅶ':
	case u'Ⅷ':
	case u'Ⅸ':
	case u'Ⅹ':
	case u'Ⅺ':
	case u'Ⅻ':
	case u'Ⅼ':
	case u'Ⅽ':
	case u'Ⅾ':
	case u'Ⅿ':
		return ch + 16;
	default:
		return ch;
	}
}
// ∑∫∪∩√∈∏
char16_t toupper(char16_t ch)
{
	switch (ch)
	{
		// English small letters:
	case u'a':
	case u'b':
	case u'c':
	case u'd':
	case u'e':
	case u'f':
	case u'g':
	case u'h':
	case u'i':
	case u'j':
	case u'k':
	case u'l':
	case u'm':
	case u'n':
	case u'o':
	case u'p':
	case u'q':
	case u'r':
	case u's':
	case u't':
	case u'u':
	case u'v':
	case u'w':
	case u'x':
	case u'y':
	case u'z':
		// English wide small letters:
	case u'ａ':
	case u'ｂ':
	case u'ｃ':
	case u'ｄ':
	case u'ｅ':
	case u'ｆ':
	case u'ｇ':
	case u'ｈ':
	case u'ｉ':
	case u'ｊ':
	case u'ｋ':
	case u'ｌ':
	case u'ｍ':
	case u'ｎ':
	case u'ｏ':
	case u'ｐ':
	case u'ｑ':
	case u'ｒ':
	case u'ｓ':
	case u'ｔ':
	case u'ｕ':
	case u'ｖ':
	case u'ｗ':
	case u'ｘ':
	case u'ｙ':
	case u'ｚ':
		// Russian small letters:
	case u'а':
	case u'б':
	case u'в':
	case u'г':
	case u'д':
	case u'е':
	case u'ж':
	case u'з':
	case u'и':
	case u'й':
	case u'к':
	case u'л':
	case u'м':
	case u'н':
	case u'о':
	case u'п':
	case u'р':
	case u'с':
	case u'т':
	case u'у':
	case u'ф':
	case u'х':
	case u'ц':
	case u'ч':
	case u'ш':
	case u'щ':
	case u'ъ':
	case u'ы':
	case u'ь':
	case u'э':
	case u'ю':
	case u'я':
		// Greek small letters:
	case u'α':
	case u'β':
	case u'γ':
	case u'δ':
	case u'ε':
	case u'ζ':
	case u'η':
	case u'θ':
	case u'ι':
	case u'κ':
	case u'λ':
	case u'μ':
	case u'ν':
	case u'ξ':
	case u'ο':
	case u'π':
	case u'ρ':
	case u'σ':
	case u'τ':
	case u'υ':
	case u'φ':
	case u'χ':
	case u'ψ':
	case u'ω':
	case u'ϊ':
	case u'ϋ':
		return ch - 32;
	case u'ς':
		return u'Σ'; // the Greek sigmar letter has two forms of small cases!
					 // Roman small digits
	case u'ⅰ':
	case u'ⅱ':
	case u'ⅲ':
	case u'ⅳ':
	case u'ⅴ':
	case u'ⅵ':
	case u'ⅶ':
	case u'ⅷ':
	case u'ⅸ':
	case u'ⅹ':
	case u'ⅺ':
	case u'ⅻ':
	case u'ⅼ':
	case u'ⅽ':
	case u'ⅾ':
	case u'ⅿ':
		return ch - 16;
	default:
		return ch;
	}
}

double pi_test(int n)
{
	double sum = 0.0;
	// #pragma omp parallel for num_threads(cpu_count()) reduction(+:sum)

	for (int i = 0; i < n; i++)
	{
		double factor;
		if (i % 2 == 0)
			factor = 1.0;
		else
			factor = -1.0;
		sum += factor / (2 * i + 1);
	}

	return 4.0 * sum;
}

Timer::Timer()
{
	start = clock();
	this->message = "reported";
}

Timer::Timer(const char *message)
{
	//	print("starting recording:", message);
	start = clock();
	this->message = message;
}

Timer::~Timer()
{
	auto end = clock();
	cout << "time cost " << double(end - start) / CLOCKS_PER_SEC << " seconds in " << message
		 << endl;
}

void Timer::report(const char *message)
{
	auto end = clock();
	cout << message << " cost " << (end - start) / CLOCKS_PER_SEC << " seconds"
		 << endl;
	start = end;
}

#include <random>
void test_priority_dict()
{
	priority_dict<String> pq;
	pq.insert(u"this");
	pq.insert(u"that");
	pq.insert(u"abc");
	pq.insert(u"def");
	pq.insert(u"ghi");
	pq.insert(u"jkl");
	pq.insert(u"mno");
	pq.insert(u"pqr");
	pq.insert(u"stu");
	pq.insert(u"vwx");
	pq.insert(u"yz");
	std::default_random_engine e;
	while (!pq.empty())
	{
		auto element = pq.map.begin()->first;
		cout << "removing " << element << endl;
		pq.erase(pq.map.begin()->first);
		pq.insert(std::toString(e()));
	}
}

String &tolower(String &s)
{
	if (s.empty())
	{
		return s;
	}
	for (auto &ch : s)
	{
		ch = tolower(ch);
	}
	return s;
}

void seed_rand()
{
	srand(time(0));
}

int nextInt(int max)
{
	return rand() % max;
}

void append_file_separator(string &workingDirectory)
{
	switch (workingDirectory.back())
	{
	case '/':
	case '\\':
		break;
	default:
		workingDirectory += '/';
	}
}
void test_set_operation()
{
	std::set<string> A{"a", "b", "c", "d"};
	std::set<string> B{"a", "b", "c", "e"};

	cout << "A = " << A << endl;
	cout << "B = " << B << endl;
	cout << "A - B = " << (A - B) << endl;
	cout << "A | B = " << (A | B) << endl;
	cout << "A & B = " << (A & B) << endl;
}

#include <unistd.h>

string getcwd()
{
	char pPath[256] = {0};
	return ::getcwd(pPath, sizeof(pPath));
}

string now()
{
	time_t t = time(0);
	char buffer[9] = {0};
	strftime(buffer, sizeof(buffer), "%H:%M:%S", localtime(&t));
	//	strftime(buffer, sizeof(buffer), "%Y-%m-%d %H:%M:%S", localtime(&t));
	return buffer;
}

BinaryFile::BinaryFile(const string &file, ByteOrder byteorder) : byteorder(byteorder)
{
	if (os_access(file))
	{
		this->file.open(file, std::ios::in | std::ios::out | std::ios::binary);
	}
	else
	{
		this->file.open(file, std::ios::out | std::ios::binary);
	}
}

int BinaryFile::getsize()
{
	size_t current_pos = file.tellg();
	file.seekg(0, std::ios::end);
	size_t ending_pos = file.tellg();
	int remaining_size = ending_pos - current_pos;

	file.seekg(-remaining_size, std::ios::cur);
	return remaining_size;
}

void BinaryFile::swap_byte_order(char *buffer, int length)
{
	for (int i = 0; i < length / 2; ++i)
	{
		std::swap(buffer[i], buffer[length - 1 - i]);
	}
}

#include <unistd.h>

bool os_access(const std::string &name, int status)
{
	return (access(name.c_str(), status) != -1);
}

bool isdigit(const String &str)
{
	for (auto ch : str)
	{
		if (!isdigit(ch))
			return false;
	}
	return true;
}

bool isdigit(char16_t ch)
{
	//	Timer timer(__PRETTY_FUNCTION__);
	switch (ch)
	{
	case u'0':
	case u'1':
	case u'2':
	case u'3':
	case u'4':
	case u'5':
	case u'6':
	case u'7':
	case u'8':
	case u'9':

	case u'０':
	case u'１':
	case u'２':
	case u'３':
	case u'４':
	case u'５':
	case u'６':
	case u'７':
	case u'８':
	case u'９':
		return true;
	default:
		return false;
	}
}
// other digits:
// '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
// '₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉',
// '①', '②', '③', '④', '⑤', '⑥', '⑦', '⑧', '⑨',
// '⑴', '⑵', '⑶', '⑷', '⑸', '⑹', '⑺', '⑻', '⑼',
// '⒈', '⒉', '⒊', '⒋', '⒌', '⒍', '⒎', '⒏', '⒐',
// '⓪', '⓵', '⓶', '⓷', '⓸', '⓹', '⓺', '⓻', '⓼', '⓽',
// '⓿', '❶', '❷', '❸', '❹', '❺', '❻', '❼', '❽', '❾',
// '➀', '➁', '➂', '➃', '➄', '➅', '➆', '➇', '➈',
// '➊', '➋', '➌', '➍', '➎', '➏', '➐', '➑', '➒',

bool isspace(char16_t ch)
{
	/**
	 * in python run the following codes:
	 *
	 *     for i in range(65536):
	 if chr(i).isspace():
	 print("case u'\\%s':" % hex(i)[1:])
	 *
	 */

	switch (ch)
	{
	case u'\x9':
	case u'\xa':
	case u'\xb':
	case u'\xc':
	case u'\xd':
	case u'\x1c':
	case u'\x1d':
	case u'\x1e':
	case u'\x1f':
	case u'\x20':
	case u'\x85':
	case u'\xa0':
	case u'\x1680':
	case u'\x2000':
	case u'\x2001':
	case u'\x2002':
	case u'\x2003':
	case u'\x2004':
	case u'\x2005':
	case u'\x2006':
	case u'\x2007':
	case u'\x2008':
	case u'\x2009':
	case u'\x200a':
	case u'\x2028':
	case u'\x2029':
	case u'\x202f':
	case u'\x205f':
	case u'\x3000':
		return true;
	default:
		return false;
	}
}

bool isxdigit(char ch)
{
	switch (ch)
	{
	case '0':
	case '1':
	case '2':
	case '3':
	case '4':
	case '5':
	case '6':
	case '7':
	case '8':
	case '9':

	case 'a':
	case 'b':
	case 'c':
	case 'd':
	case 'e':
	case 'f':

	case 'A':
	case 'B':
	case 'C':
	case 'D':
	case 'E':
	case 'F':
		return true;
	default:
		return false;
	}
}

bool isSpaceChar(char16_t ch)
{
	/**
	 * in java: run the following codes
	 for (int i = 0; i < 65536; ++i) {
	 char ch = (char)i;
	 if (Character.isSpaceChar(ch)) {
	 System.err.printf("case u'\\x%x':\n", i);
	 }
	 }
	 *
	 */

	switch (ch)
	{
	case u'\x20':
	case u'\xa0':
	case u'\x1680':
	case u'\x180e':
	case u'\x2000':
	case u'\x2001':
	case u'\x2002':
	case u'\x2003':
	case u'\x2004':
	case u'\x2005':
	case u'\x2006':
	case u'\x2007':
	case u'\x2008':
	case u'\x2009':
	case u'\x200a':
	case u'\x2028':
	case u'\x2029':
	case u'\x202f':
	case u'\x205f':
	case u'\x3000':
		return true;
	default:
		return false;
	}
}

vector<char16_t> toCharArray(const char16_t *s, int length)
{
	return vector<char16_t>(s, s + length);
}

range::range(int start, int stop, int step) : start(start), stop(stop), step(step)
{
	if (step > 1)
	{
		if (stop < start)
		{
			stop = start;
		}
		else if (stop > start)
		{
			// adjust stop value so that : stop - start ≡ 0 [MOD step]
			int rem = (stop - start) % step;
			if (rem)
				stop += step - rem;
		}
	}
	else if (step < 0)
	{
		if (stop > start)
		{
			stop = start;
		}
		else if (stop < start)
		{
			// adjust stop value so that : start - stop ≡ 0 [MOD step]
			int rem = (start - stop) % -step;
			if (rem)
				stop -= rem;
		}
	}
}
range::range(int start, int stop) : start(start), stop(stop), step(1) {}
range::range(int stop) : start(0), stop(stop), step(1) {}

int range::size() const
{
	return ceiling(stop - start, step);
}

range::iterator range::begin() const
{
	return {start, step};
}

int range::operator[](int i) const
{
	return start + i * step;
}

range::iterator range::end() const
{
	return {stop, step};
}

range::iterator &range::iterator::operator++()
{
	index += step;
	return *this;
}

bool range::iterator::operator!=(iterator &other)
{
	return this->index != other.index;
}

int range::iterator::operator*()
{
	return index;
}

std::set<int> range::set() const
{
	std::set<int> s;
	for (auto x : *this)
	{
		s.insert(x);
	}
	return s;
}

std::ostream &operator<<(std::ostream &cout, const range &indices)
{
	return cout << indices.start << ":" << indices.stop;
}

int mod(int a, int b)
{
	if (a < 0)
	{
		if (b < 0)
			return -(-a % -b);
		return b - (-a) % b;
	}

	if (b < 0)
		return a % -b + b;
	return a % b;
}

int floor(int a, int b)
{
	if (b < 0)
	{
		a = -a;
		b = -b;
	}

	if (a < 0)
	{
		return -ceiling(-a, b);
	}
	return a / b;
}

int ceiling(int a, int b)
{
	if (b < 0)
	{
		a = -a;
		b = -b;
	}

	if (a < 0)
	{
		return -floor(-a, b);
	}

	int q = a / b;
	int r = a % b;
	if (r)
		return q + 1;
	return q;
}

std::string json_encode(std::string s)
{
	string prefix;
	while (!s.empty() && !TextC::utf8ByteSize(s[0]))
	{
		prefix += "\\" + hex(s[0]).substr(1);
		s = s.substr(1);
	}

	string suffix;
	for (int i : range((int)s.size() - 1, -1, -1))
	{
		int utf8ByteSize = TextC::utf8ByteSize(s[i]);
		if (utf8ByteSize && s.size() - i < utf8ByteSize)
		{
			for (int j : range(i, s.size()))
				suffix += "\\" + hex(s[j]).substr(1);
			s = s.substr(0, i);
			break;
		}
	}

	str_replace("\n", "\\n", s);
	str_replace("\"", "\\\"", s);

	if (!prefix.empty())
	{
		while (!s.empty() && isxdigit(s[0]))
		{
			prefix += "\\" + hex(s[0]).substr(1);
			s = s.substr(1);
		}
		s = prefix + s;
	}

	if (!suffix.empty())
		s += suffix;
	return '"' + s + '"';
}

/*
vector<string> listdir(const string &dir) {
	return listdir(dir.c_str());
}

vector<string> listdir(const char *dir) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(dir);

	vector<string> result;
	intptr_t handle;
	_finddata_t findData;

	string filespec = dir;
	char last = filespec.back();
	switch (last) {
	case '\\':
	case '/':
		break;
	default:
		filespec += "/";
	}

	filespec += "*.*";

	handle = _findfirst(filespec.c_str(), &findData);
	if (handle < 0)
		return result;

	do {
		print(findData.name);
		if (findData.attrib & _A_SUBDIR) {
			if (!strcmp(findData.name, ".") || !strcmp(findData.name, ".."))
				continue;
			result.push_back(findData.name);
		} else {
			result.push_back(findData.name);
		}

	} while (_findnext(handle, &findData) == 0);

	_findclose(handle);
//	print(result);
	return result;
}
*/

extern "C"
{

	int sizeof_string()
	{
		return sizeof(string);
	}

	void *construct(size_t n)
	{
		return operator new(n);
	}

	void destruct(void *p)
	{
		operator delete(p);
	}

	string unicode2utf8(int wc)
	{
		char cstr[7];
		Text::unicode2utf(wc, cstr);
		return cstr;
	}
}

std::string bin(int n)
{
	vector<string> bits;
	while (n && 0xff)
	{
		bits.push_back(std::bitset<8>(n & 0xff).to_string());
		n >>= 8;
	}

	reverse(bits.begin(), bits.end());
	return "0b" + join("'", bits);
}

std::string hex(int n)
{
	std::stringstream ss;
	ss << std::hex << n;	// Convert to hex and store in stringstream
	return "0x" + ss.str(); // Get the hex string
}

std::string hex(char n)
{
	return hex((int)(unsigned char)n);
}

void generate_permutations(int n, std::function<void(const vector<int> &)> fn)
{
	vector<int> perm(n);
	// positions are 1-based for elements
	vector<int> pos(n + 1);
	// directions initialized to -1 (left)
	vector<int> dir(n + 1, -1);

	// Initialize permutation and positions
	for (int i = 0; i < n; ++i)
	{
		perm[i] = i + 1;
		pos[i + 1] = i;
	}
	dir[1] = 0; // first element has direction 0

	while (true)
	{
		fn(perm);
		// Find the largest element with non-zero direction
		int m = -1;
		for (int i = n; i >= 1; --i)
		{
			if (dir[i] != 0)
			{
				m = i;
				break;
			}
		}
		if (m == -1)
			break; // No more permutations

		int current_pos = pos[m];
		int next_pos = current_pos + dir[m];

		// Swap m with the adjacent element
		int k = perm[next_pos];
		swap(perm[current_pos], perm[next_pos]);
		swap(pos[m], pos[k]); // Update positions of m and the swapped element

		// Check if m should stop moving
		bool at_edge = (next_pos == 0 && dir[m] == -1) || (next_pos == n - 1 && dir[m] == 1);
		bool next_larger = false;
		if (!at_edge)
		{
			int neighbor_pos = next_pos + dir[m];
			if (neighbor_pos >= 0 && neighbor_pos < n)
			{
				int neighbor = perm[neighbor_pos];
				if (neighbor > m)
					next_larger = true;
			}
		}
		if (at_edge || next_larger)
			dir[m] = 0;

		// Update directions for elements larger than m
		for (int i = m + 1; i <= n; ++i)
			dir[i] = pos[i] < pos[m]? 1: -1;
	}
}