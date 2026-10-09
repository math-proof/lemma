#pragma once
//gcc -Werror=return-local-addr
#pragma GCC diagnostic error "-Wreturn-local-addr"
#pragma GCC diagnostic error "-Wreturn-type"
#pragma GCC diagnostic error "-Wmultichar"
#pragma GCC diagnostic error "-Wunused-value"

#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wparentheses"

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include<iomanip>
using std::vector;
#include <iterator>
#include <regex>
#include <algorithm>
#include <cstdint>
//#define __log(symbol) std::cout << #symbol << " = \n" << (symbol) << std::endl;
//#define __print(symbol) std::cout << #symbol << " = " << (symbol) << std::endl;
//#define __println(symbol) std::cout << #symbol << " = \n" << (symbol) << std::endl;

using qword = unsigned long long;
using BYTE = unsigned char;
using word = unsigned short;
using dword = unsigned int;
static_assert(sizeof(void *) == 8, "only 64-bit code generation is supported!");
static_assert(sizeof(BYTE) == 1, "sizeof(BYTE) must be 1");
static_assert(sizeof(word) == 2, "sizeof(word) must be 2");
static_assert(sizeof(dword) == 4, "sizeof(dword) must be 4");
static_assert(sizeof(qword) == 8, "sizeof(qword) must be 8");

template<typename _Ty, int b = 2>
struct color_ptr {
	static const qword MASK = (1 << b) - 1;
	using _Myt = color_ptr;
	using value_type = _Ty;
	friend std::ostream& operator <<(std::ostream &cout, const _Myt &p) {
		if (!p)
			cout << "nullptr";
		else
			; // cout << *p;
		return cout << ",\t" << std::boolalpha << p.color;
	}

	//postcondition: return a valid pointer
	operator value_type*() {
		return reptr();
	}

	operator const value_type*() const {
		return (const value_type*) reptr();
	}

	color_ptr() {
		value = 0;
	}

	explicit color_ptr(value_type *ptr, BYTE color = 0) {
		this->reptr(ptr);
		this->color = color;
	}

	//_Myt &operator = (value_type *ptr) {
	//	this->ptr = ptr;
	//	return *this;
	//}

	bool operator <(const _Myt &y) const {
		return reptr() < y.reptr();
	}

	bool operator ==(const _Myt &y) const {
		return value == y.value;
	}

	bool operator ==(const value_type *ptr) const {
		return this->reptr() == reptr();
	}

	bool operator ==(value_type *ptr) const {
		return this->reptr() == reptr();
	}

	bool operator !() const {
		return !reptr();
	}

	const value_type* operator ->() const {
		return operator const value_type*();
	}

	value_type* operator ->() {
		return operator value_type*();
	}

	value_type* reptr() const {
		return (value_type*) (value & ~MASK);
	}

	void reptr(value_type *ptr) {
		(value &= MASK) |= (qword) ptr;
		//		return ptr;
	}

	union {
		mutable BYTE color :b;
		mutable qword value = 0;
	};
};

template<typename _Ty>
struct object: color_ptr<_Ty> {
	using _Myt = object;
	using element_type = _Ty;
//	size_t hashCode() const {
//		return ::hashCode(reptr());
//	}

	object(const _Myt &y) :
			color_ptr<_Ty>(y) {
		y.color = true;
	}

	_Myt& operator =(const _Myt &y) {
		_Myt tmp = *this;
		return *::new (this) _Myt(y);
	}

	object(_Ty *ptr = 0) :
			color_ptr<_Ty>(ptr) {
	}

	_Myt& operator =(_Ty *y) {
		this->~object();
		return *::new (this) _Myt(y);
	}

	bool operator <(const _Myt &y) const {
		return *this->reptr() < *y.reptr();
	}

	bool operator ==(const _Myt &y) const {
		return *this->reptr() == *y.reptr();
	}

	template<typename T> _Myt& operator +=(T &y) {
		this->reptr(&(*this->reptr() + y));
		return *this;
	}
	template<typename T> _Myt& operator -=(T &y) {
		this->reptr(&(*this->reptr() - y));
		return *this;
	}
	template<typename T> _Myt& operator *=(T &y) {
		this->reptr(&(*this->reptr() * y));
		return *this;
	}
	template<typename T> _Myt& operator /=(T &y) {
		this->reptr(&(*this->reptr() / y));
		return *this;
	}
	template<typename T> _Myt& operator %=(T &y) {
		this->reptr(&(*this->reptr() % y));
		return *this;
	}
	template<typename T> _Myt& operator &=(T &y) {
		this->reptr(&(*this->reptr() & y));
		return *this;
	}
	template<typename T> _Myt& operator |=(T &y) {
		this->reptr(&(*this->reptr() | y));
		return *this;
	}
	template<typename T> _Myt& operator ^=(T &y) {
		this->reptr(&(*this->reptr() ^ y));
		return *this;
	}

	~object() {
		auto ptr = this->reptr();
		if (this->color || !ptr)
			return;
		delete ptr;
	}

	template<typename T>
	T* instanceof() {
		return dynamic_cast<T*>(this->reptr());
	}

	template<typename T>
	const T* instanceof() const {
		return dynamic_cast<const T*>(this->reptr());
	}
};

using std::ifstream;
using std::ostringstream;
using std::istringstream;
using std::stringstream;
using std::ofstream;
using std::ios;

#include <unordered_map>
template<typename KEY, typename VALUE>
using dict = std::unordered_map<KEY, VALUE>;

#include <map>

#include <string>
using std::string;

using String = std::u16string;

#include <iostream>
using std::cout;
using std::cerr;
using std::endl;

#include <assert.h>

template<typename _Tx, typename _Ty>
std::ostream& operator <<(std::ostream &cout, const std::pair<_Tx, _Ty> &v) {
	cout << '(';
	cout << v.first << ", " << v.second;
	cout << ')';
	return cout;
}

template<typename _Ty>
std::ostream& operator <<(std::ostream &cout, const vector<_Ty> &v) {
	cout << '[';
	if (!v.empty()) {
		cout << v[0];
		for (size_t i = 1; i < v.size(); ++i) {
			cout << ", " << v[i];
		}
	}

	cout << ']';
	return cout;
}

template<typename _Ty>
std::ostream& operator <<(std::ostream &cout, const vector<vector<_Ty>> &v) {
	cout << '[';
	if (!v.empty()) {
		cout << "\n\t" << v[0];
		for (size_t i = 1; i < v.size(); ++i) {
			cout << ",\n\t" << v[i];
		}
	}

	cout << "\n]";
	return cout;
}

#include <array>
template<typename _Ty, std::size_t _Nm>
std::ostream& operator <<(std::ostream &cout, const std::array<_Ty, _Nm> &v) {
	cout << '[';
	if (!v.empty()) {
		cout << v[0];
		for (size_t i = 1; i < v.size(); ++i) {
			cout << ", " << v[i];
		}
	}

	cout << ']';
	return cout;
}

#include <set>
template<typename _Ty>
std::ostream& operator <<(std::ostream &cout, const std::set<_Ty> &v) {
	cout << '{';
	bool initial = true;
	for (auto &e : v) {
		if (initial) {
			cout << e;
			initial = false;
		} else
			cout << ", " << e;
	}

	cout << '}';
	return cout;
}

#include <unordered_set>
template<typename _Ty>
std::ostream& operator <<(std::ostream &cout,
		const std::unordered_set<_Ty> &v) {
	cout << '{';
	bool initial = true;
	for (auto &e : v) {
		if (initial) {
			cout << e;
			initial = false;
		} else
			cout << ", " << e;
	}

	cout << '}';
	return cout;
}

template<typename _Key, typename _Ty>
std::ostream& operator <<(std::ostream &cout, const dict<_Key, _Ty> &map) {
	cout << '{';
	bool initial = true;
	for (auto &p : map) {
		if (initial) {
			initial = false;
		} else
			cout << ", ";
		cout << p.first << " : " << p.second;
	}

	cout << '}';
	return cout;
}

template<typename _Key, typename _Ty>
std::ostream& operator <<(std::ostream &cout, const std::map<_Key, _Ty> &map) {
	cout << '{';
	bool initial = true;
	for (auto &p : map) {
		if (initial) {
			initial = false;
		} else
			cout << ", ";
		cout << p.first << " : " << p.second;
	}

	cout << '}';
	return cout;
}

template<typename _Ty>
_Ty gcd(_Ty x, _Ty y) {
	if (!y)
		return x;
	return gcd(y, x % y);
}

struct Text {
	struct iterator {
		iterator(Text *text, bool eof);
		Text *text;
		bool eof = true;

		iterator& operator++();
		bool operator!=(iterator &other);
		String& operator*();
	};

	String line;
	static int surrogate_pairs(int unicode);
	static uint32_t surrogate_pairs_s(uint32_t unicode);

	iterator begin();
	iterator end();

	Text(const string &file);
	ifstream file;

	vector<String> readlines();
	Text& operator >>(int &unicode);
	Text& operator >>(String &v);
	Text& operator >>(vector<String> &v);
	Text& operator >>(dict<String, int> &word2id);
	Text& operator >>(dict<char16_t, int> &word2id);
	dict<String, int> read_vocab(int index = 2);
	dict<string, int> read_vocab_cstr();

	dict<String, int>& read_vocab(dict<String, int> &word2id, int index = 2);
	dict<string, int>& read_vocab(dict<string, int> &word2id, int index = 2);

	dict<char16_t, int> read_vocab_char();
	String toString();
	operator bool();

	static int utf2unicode(const char *pText, int length);
	static String& append_unicode(String &s, int unicode);
	static const char* unicode2utf(int wc, char *pText);
	static string unicode2utf(const String &wstr);
	static string unicode2gbk(const String &wstr);
	static void test_utf_unicode_conversion();
};

struct TextC {
	struct iterator {
		iterator(TextC *text, bool eof);
		TextC *text;
		bool eof = true;

		iterator& operator++();
		bool operator!=(iterator &other);
		string& operator*();
	};

	string line;

	iterator begin();
	iterator end();

	TextC(const string &file);
	ifstream file;

	vector<string> readlines();
	TextC& operator >>(string &v);
	TextC& operator >>(vector<string> &v);
	TextC& operator >>(dict<string, int> &word2id);
	dict<string, int> read_vocab(int index = 2);
	dict<string, int> read_vocab_cstr();
	dict<string, int>& read_vocab(dict<string, int> &word2id, int index = 2);

	dict<char, int> read_vocab_char();
	string toString();
	operator bool();

	static char get_bits(char ch, int start, int size, int shift = 0);
	static char get_bits(char ch, int start, int size, char _ch);
	static char get_bits(char ch, int start, int size, char _ch, int _size);
	static size_t utf8ByteSize(unsigned char byte);
	string read() const;
};

void print();

template<typename X, typename ...W>
void print(const X &x, const W& ...args) {
	std::cout << x << " ";
	print(args...);
}

//C/C++ is little_endian but Java is big_endian;
enum class ByteOrder : int {
	native, little_endian, big_endian,
};

struct BinaryFile {
	BinaryFile(const string &file, ByteOrder byteorder =
			ByteOrder::little_endian);

	int getsize();

	static void swap_byte_order(char *buffer, int length);

	template<typename Ty>
	static void swap_byte_order(vector<Ty> &value) {
		for (Ty &v : value) {
			swap_byte_order((char*) &v, sizeof(Ty));
		}
	}

	ByteOrder byteorder;
	std::fstream file;

	template<typename Ty>
	BinaryFile& operator >>(vector<Ty> &value) {
		file.read((char*) &value[0], sizeof(Ty) * value.size());

		if (this->byteorder == ByteOrder::big_endian) {
			swap_byte_order(value);
		}

		return *this;
	}

	template<typename Ty>
	BinaryFile& operator >>(vector<vector<Ty>> &value) {
		for (auto &v : value) {
			*this >> v;
		}

		return *this;
	}

	template<typename Ty>
	BinaryFile& operator >>(vector<vector<vector<Ty>>> &value) {
		for (auto &v : value) {
			*this >> v;
		}

		return *this;
	}

	template<typename Ty>
	BinaryFile& operator <<(const vector<Ty> &value) {
		switch (this->byteorder) {
		case ByteOrder::big_endian: {
			auto _value = value;
			swap_byte_order(_value);
			file.write((const char*) &_value[0], sizeof(Ty) * value.size());
		}
			break;
		case ByteOrder::native:
		case ByteOrder::little_endian:
			file.write((const char*) &value[0], sizeof(Ty) * value.size());
			break;
		default:
			print(__PRETTY_FUNCTION__);
			throw;
		}

		return *this;
	}

	template<typename Ty>
	BinaryFile& operator >>(Ty &value) {
		file.read((char*) &value, sizeof(Ty));
		if (this->byteorder == ByteOrder::big_endian) {
			swap_byte_order((char*) &value, sizeof(Ty));
		}
		return *this;
	}

	template<typename Ty>
	BinaryFile& operator <<(const Ty &value) {
		switch (this->byteorder) {
		case ByteOrder::big_endian: {
			auto _value = value;
			auto buffer = (char*) &_value;
			swap_byte_order(buffer, sizeof(Ty));
			file.write(buffer, sizeof(Ty));
		}
			break;
		case ByteOrder::native:
		case ByteOrder::little_endian:
			file.write((const char*) &value, sizeof(Ty));
			break;
		default:
			print(__PRETTY_FUNCTION__)
			;
			throw;
		}

		return *this;
	}
};

std::ostream& operator <<(std::ostream &cout, const String &v);
using bytes = std::basic_string<unsigned char>;
std::ostream& operator <<(std::ostream &cout, const bytes &str);

struct range {
	range(int start, int stop, int step);
	range(int start, int stop);
	range(int stop);
	int start;
	int stop;
	int step;
	int size() const;

	struct iterator {
		int index;
		int step;

		iterator& operator++();
		bool operator!=(iterator &other);
		int operator*();
	};

	int operator [](int i) const;
	iterator begin() const;
	iterator end() const;

	std::set<int> set() const;

	template<typename UFN>
	auto list(const UFN &fn) {
		vector<decltype(fn(1))> v;
		for (int x : *this) {
			v.push_back(fn(x));
		}
		return v;
	}
};

std::ostream& operator <<(std::ostream &cout, const range &indices);

template<typename _Container>
struct enumerate {
	_Container &c;
	using _Ty = typename _Container::iterator::value_type;
	enumerate(_Container &c): c(c){
	}

	int size() const {
		return c.size();
	}

	int empty() const {
		return c.empty();
	}

	struct Tuple {
		Tuple(int index, _Ty &value):
			index(index), value(value) {}

		int index;
		_Ty &value;
	};

	struct iterator {
		int index;
		typename _Container::iterator iter;

		iterator& operator++() {
			++index;
			++iter;
			return *this;
		}

		bool operator!=(iterator &other) {
			return index != other.index;
		}

		Tuple operator*() {
			return Tuple(index, *iter);
		}
	};

	iterator begin() {
		return {0, c.begin()};
	}

	iterator end() {
		return {(int)c.size(), c.end()};
	}
};

String operator +(const String &lhs, int rhs);

vector<String> split(const String &in);
vector<string> split(const string &in);
vector<string> split(const string &in, char separator);

template<typename _CharT>
std::basic_string<_CharT> join(const std::basic_string<_CharT> &delim,
		const vector<std::basic_string<_CharT>> &val) {
	std::basic_string<_CharT> str;
	for (auto &e : val) {
		if (!str.empty())
			str += delim;

		str += e;
	}
	return str;
}

template<typename _CharT>
std::basic_string<_CharT> join(const std::basic_string<_CharT> &delim,
		const std::set<std::basic_string<_CharT>> &val) {
	std::basic_string<_CharT> str;
	for (auto &e : val) {
		if (!str.empty())
			str += delim;

		str += e;
	}
	return str;
}

template<typename _CharT>
std::basic_string<_CharT> join(const _CharT *delim,
		const vector<std::basic_string<_CharT>> &val) {
	return join(std::basic_string<_CharT>(delim), val);
}

template<typename _CharT>
std::basic_string<_CharT> join(const _CharT *delim,
		const std::set<std::basic_string<_CharT>> &val) {
	return join(std::basic_string<_CharT>(delim), val);
}

template<typename _CharT>
bool startsWith(const std::basic_string<_CharT> &str,
		const std::basic_string<_CharT> &start) {
	auto startlen = start.size();
	return str.size() >= startlen && str.substr(0, startlen) == start;
}

template<typename _CharT>
bool endsWith(const std::basic_string<_CharT> &str,
		const std::basic_string<_CharT> &end) {
	auto lenLength = end.size();
	return str.size() >= lenLength && str.substr(lenLength, str.length()) == end;
}

#include "wchar.h"
bool isspace(char16_t ch);
bool isSpaceChar(char16_t ch);
bool isdigit(char16_t ch);
bool isxdigit(char ch);
bool isdigit(const String &str);

template<typename _CharT>
std::basic_string<_CharT>& strip(std::basic_string<_CharT> &s) {
	if (s.empty()) {
		return s;
	}

	typename std::basic_string<_CharT>::iterator c;

	// Erase whitespace before the string

	for (c = s.begin(); c != s.end() && isspace(*c++);)
		;
	s.erase(s.begin(), --c);

	// Erase whitespace after the string

	for (c = s.end(); c != s.begin() && isspace(*--c);)
		;
	s.erase(++c, s.end());
	return s;
}

template<typename _CharT>
std::basic_string<_CharT>& lstrip(std::basic_string<_CharT> &s) {
	if (s.empty()) {
		return s;
	}

	typename std::basic_string<_CharT>::iterator c;

	// Erase whitespace before the string

	for (c = s.begin(); c != s.end() && isspace(*c++);)
		;
	s.erase(s.begin(), --c);

	return s;
}

char16_t tolower(char16_t ch);

char16_t toupper(char16_t ch);

String& tolower(String &s);

string& tolower(string &s);

template<typename _Ty>
vector<_Ty>& operator <<(vector<_Ty> &out, const vector<_Ty> &in) {
	out.insert(out.end(), in.begin(), in.end());
	return out;
}

template<typename _Ty, typename InputType>
vector<_Ty>& operator <<=(vector<_Ty> &out,
		std::initializer_list<InputType> in) {
	out.insert(out.end(), in.begin(), in.end());
	return out;
}


template<typename _Ty>
bool operator !(const vector<_Ty> &x) {
	return x.empty();
}

template<typename _CharT>
bool operator !(const std::basic_string<_CharT> &s) {
	return s.empty();
}

namespace std {
int strlen(const String &value);

String toString(int);
String toString(const char *s);
String toString(const string &s);
vector<String> toStrings(const vector<string> &s);
vector<vector<String>> toStrings(const vector<vector<string>> &s);

string to_string(const String &s);

template<typename _Ty>
vector<_Ty> sample(vector<_Ty> v, int size) {
	int v_size = v.size();
	for (int i = 0; i < size; ++i) {
		int j = i + rand() % (v_size - i);
		std::swap(v[i], v[j]);
	}
	v.resize(size);
	return v;
}
}

#include <limits>
template<typename _Ty>
_Ty maximum(const vector<_Ty> &v) {
	_Ty max = std::numeric_limits<_Ty>::min();
	for (auto &x : v) {
		if (x > max)
			max = x;
	}
	return max;
}

template<typename _Ty>
_Ty minimum(const vector<_Ty> &v) {
	_Ty min = std::numeric_limits<_Ty>::max();
	for (auto &x : v) {
		if (x < min)
			min = x;
	}
	return min;
}

#include <queue>
#include <forward_list>

template<typename _Ty>
vector<_Ty>& addAll(vector<_Ty> &out, const vector<_Ty> &in) {
	out.insert(out.end(), in.begin(), in.end());
	return out;
}

template<typename _Ty>
std::vector<_Ty> list(const std::set<_Ty> &c) {
	std::vector<_Ty> v;
	for (const auto &x : c) {
		v.push_back(x);
	}
	return v;
}

template<typename UFN, typename _Ty>
auto list(const UFN &fn, const std::vector<_Ty> &c) {
	vector<decltype(fn(_Ty()))> v;
	for (const auto &x : c) {
		v.push_back(fn(x));
	}
	return v;
}

template<typename UFN, typename _Ty>
auto list(const UFN &fn, const std::set<_Ty> &c) {
	vector<decltype(fn(_Ty()))> v;
	for (const auto &x : c) {
		v.push_back(fn(x));
	}
	return v;
}

template<typename T>
int indexOf(const vector<T> &elementData, const T &o, int index = 0) {
	for (int i = index, size = elementData.size(); i < size; ++i)
		if (o == elementData[i])
			return i;
	return -1;
}

template<typename T>
vector<T> concatExcept(const vector<T> &arr, size_t i) {
	vector<T> arrNew(arr.size() - 1);
	int index = 0;
	for (size_t j = 0; j < arr.size(); ++j) {
		if (i != j)
			arrNew[index++] = arr[j];
	}
	return arrNew;
}

template<typename T>
bool contains(const vector<T> &elementData, const T &o) {
	return indexOf(elementData, o) >= 0;
}

const double oo = std::numeric_limits<double>::infinity();

#ifdef _DEBUG
#define __debug(symbol) //__log(symbol)
#define assert_gt(x, y) //if (x > y){}else{std::cout << #x << " > " << #y << std::endl; __debug(x);__debug(y);}
#define assert_lt(x, y) //if (x < y){}else{std::cout << #x << " < " << #y << std::endl; __debug(x);__debug(y);}
#define assert_le(x, y) //if (x <= y){}else{std::cout << #x << " <= " << #y << std::endl; __debug(x);__debug(y);}
#define assert_ge(x, y) //if (x >= y){}else{std::cout << #x << " >= " << #y << std::endl; __debug(x);__debug(y);}
#define assert_eq(x, y) //if (x == y){}else{std::cout << #x << " == " << #y << std::endl; __debug(x);__debug(y);}
#define assert_neq(x, y) //if (x != y){}else{std::cout << #x << " != " << #y << std::endl; __debug(x);__debug(y);}
#define assert_true(expr) //if (expr){}else{std::cout << #expr << " is true " << std::endl; __debug(expr);}
#define assert_false(expr) //if (!expr){}else{std::cout << #expr << " is false " << std::endl; __debug(expr);}
#define assert_not(expr) //if (not expr){}else{std::cout << #expr << " is false " << std::endl; __debug(expr);}
#define assert_or(x, y) //if (x || y){}else{std::cout << #x << " || " << #y << std::endl; __debug(x);__debug(y);}
#define assert_and(x, y) //if (x && y){}else{std::cout << #x << " && " << #y << std::endl; __debug(x);__debug(y);}
#else
#pragma GCC diagnostic ignored "-Wunused-variable"
#define __debug(symbol)
#define assert_gt(x, y)
#define assert_lt(x, y)
#define assert_le(x, y)
#define assert_ge(x, y)
#define assert_eq(x, y)
#define assert_neq(x, y)
#define assert_true(expr)
#define assert_false(expr)
#define assert_or(x, y)
#define assert_and(x, y)
#endif

#define ensure_gt(x, y) if (x > y){}else{std::cout << #x << " > " << #y << std::endl; __debug(x);__debug(y); throw;}
#define ensure_lt(x, y) if (x < y){}else{std::cout << #x << " < " << #y << std::endl; __debug(x);__debug(y); throw;}
#define ensure_le(x, y) if (x <= y){}else{std::cout << #x << " <= " << #y << std::endl; __debug(x);__debug(y); throw;}
#define ensure_ge(x, y) if (x >= y){}else{std::cout << #x << " >= " << #y << std::endl; __debug(x);__debug(y);throw;}
#define ensure_eq(x, y) if (x == y){}else{std::cout << #x << " == " << #y << std::endl; __debug(x);__debug(y);throw;}
#define ensure_neq(x, y) if (x != y){}else{std::cout << #x << " != " << #y << std::endl; __debug(x);__debug(y);throw;}
#define ensure_true(expr) if (expr){}else{std::cout << #expr << " should be true, in " << __PRETTY_FUNCTION__ << std::endl; __debug(expr);throw;}
#define ensure_false(expr) if (!expr){}else{std::cout << #expr << " should be false, in " << __PRETTY_FUNCTION__ << std::endl; __debug(expr);throw;}
#define ensure_not(expr) if (not expr){}else{std::cout << #expr << " should be false, in " << __PRETTY_FUNCTION__ << std::endl; __debug(expr);throw;}
#define ensure_or(x, y) if (x or y){}else{std::cout << #x << " || " << #y << std::endl; __debug(x);__debug(y);throw;}
#define ensure_and(x, y) if (x and y){}else{std::cout << #x << " && " << #y << std::endl; __debug(x);__debug(y);throw;}

struct Timer {
	Timer();
	Timer(const char *message);
	const char *message;
	clock_t start;
	~Timer();
	void report(const char *message);
};

// implements a maximum priority queue;
template<typename _Ty, typename _Pr = std::less<_Ty>>
struct priority_queue: std::vector<_Ty> {
	priority_queue() {
	}
	priority_queue(std::vector<_Ty> &c) :
			std::vector<_Ty>(c) {
		// make non-trivial [_First, _Last) into a heap, using _Pred
		int _Top = this->size() >> 1;
		while (0 < _Top--) {
			int _Hole = _Top;
			adjust_heap(_Hole, _Pred);
		}
	}

	void insert(const _Ty &_Val) {	// push operation;
		int _Hole = this->size();
		this->push_back(_Val);
		push_heap(_Hole, 0, _Val, _Pred);
	}

	//precondition : size > 0 && _Where < size;
	_Ty erase(int _Where = 0) {
		int size = this->size();
		assert(_Where < size);
//		if (_Where >= size()) {
//			throw std::exception("_Where < size in " __FUNCTION__, __LINE__);
//		}
		const _Ty &_Val = (*this)[_Where];
		const _Ty &end = this->back();
		--size;
		this->pop_back();
		if (_Where != size) {
			(*this)[_Where] = end;
			adjust_heap(_Where, _Pred);
		}

		return _Val;
	}

	_Pr _Pred;	// the comparator functor
protected:

	void mov(int &_Hole, int _Idx) {
		(*this)[_Hole] = (*this)[_Idx];
		_Hole = _Idx;
	}

	// precondition: ptr[_Hole] is the element to be adjusted;
	void adjust_heap(int &_Hole, _Pr &_Pred) { // percolate _Hole to _Bottom, then push _Val, using _Pred
		_Ty _Val = (*this)[_Hole];
		int _Top = _Hole;
		int _Idx = _Hole;
		int size = this->size();
		while ((++_Idx <<= 1) < size) { // move _Hole down to larger kinder
			if (_Pred((*this)[_Idx], (*this)[_Idx - 1]))
				--_Idx;
			mov(_Hole, _Idx);
		}
		if (_Idx == size) // only kinder at bottom, move _Hole down to it
			mov(_Hole, --_Idx); // a possible bug here, _Top and _Hole might still be the same, thus overwriting ptr[_Top] which must be used as an argument in the push_heap function call;
		push_heap(_Hole, _Top, _Val, _Pred);
	}

	void push_heap(int &_Hole, int _Top, const _Ty &_Val, _Pr &_Pred) { // percolate _Hole to _Top or where _Val belongs
		auto _Idx = _Hole;
		while (_Top < _Idx && _Pred((*this)[--_Idx >>= 1], _Val)) // move _Hole up to parent
			mov(_Hole, _Idx);
		(*this)[_Hole] = _Val;    // drop _Val into final hole
	}
};

//template <typename _Ty, typename _Pr>
//_Pr priority_queue<_Ty, _Pr>::_Pred;

// implements a maximum priority queue whose elements are unique keys, ie, no duplicate items;
template<typename _Ty, typename _Pr = std::less<_Ty>>
struct priority_dict: std::vector<_Ty> {
	priority_dict() {
	}
	priority_dict(const _Pr &_Pred) :
			_Pred(_Pred) {
	}

	priority_dict(const std::set<_Ty> &c) :
			std::vector<_Ty>(c.begin(), c.end()) {
		// make non-trivial [_First, _Last) into a heap, using _Pred
		int size = this->size();
		for (int i = 0; i < size; ++i) {
			this->map[(*this)[i]] = i;
		}

		int _Top = size >> 1;
		while (0 < _Top--) {
			int _Hole = _Top;
			adjust_heap(_Hole, _Pred);
		}
	}

	void insert(const _Ty &_Val) {    // push operation;
		if (map.count(_Val))
			return;
		int _Hole = this->size();
		this->push_back(_Val);
		map[_Val] = _Hole;
		push_heap(_Hole, 0, _Val, _Pred);
//		validity_check();
	}

	void erase(const _Ty &x) {
		if (!map.count(x))
			return;
		int index = map[x];
		map.erase(x);
		erase_indexed(index);
//		validity_check();
	}

	_Ty pop() {
		int index = 0;
		_Ty x = (*this)[index];
		map.erase(x);
		erase_indexed(index);
//		validity_check();
		return x;
	}

	//precondition : size > 0 && _Where < size;
	void erase_indexed(int _Where = 0) {
		int size = this->size();
		assert(_Where < size);

//		_Ty _Val = (*this)[_Where];
		const _Ty &end = this->back();
		--size;

		if (_Where != size) {
			(*this)[_Where] = end;
			map[end] = _Where;
			this->pop_back();

			adjust_heap(_Where, _Pred);
		} else
			this->pop_back();
//		return _Val;
	}

	dict<_Ty, int> map;
	_Pr _Pred;	// the comparator functor
protected:
	void validity_check() {
		assert(map.size() == this->size());
		for (const auto &p : map) {
			if ((*this)[p.second] != p.first) {
				throw std::exception("(*this)[p.second] != p.first");
			}
		}
	}

	void mov(int &_Hole, int _Idx) {
		(*this)[_Hole] = (*this)[_Idx];
		map[(*this)[_Idx]] = _Hole;
		_Hole = _Idx;
	}

	// precondition: ptr[_Hole] is the element to be adjusted;
	void adjust_heap(int &_Hole, _Pr &_Pred) { // percolate _Hole to _Bottom, then push _Val, using _Pred
		_Ty _Val = (*this)[_Hole];
		int _Top = _Hole;
		int _Idx = _Hole;
		int size = this->size();
		while ((++_Idx <<= 1) < size) { // move _Hole down to larger kinder
			if (_Pred((*this)[_Idx], (*this)[_Idx - 1]))
				--_Idx;
			mov(_Hole, _Idx);
		}
		if (_Idx == size) // only kinder at bottom, move _Hole down to it
			mov(_Hole, --_Idx); // a possible bug here, _Top and _Hole might still be the same, thus overwriting ptr[_Top] which must be used as an argument in the push_heap function call;
		push_heap(_Hole, _Top, _Val, _Pred);
	}

	void push_heap(int &_Hole, int _Top, const _Ty &_Val, _Pr &_Pred) { // percolate _Hole to _Top or where _Val belongs
		auto _Idx = _Hole;
		while (_Top < _Idx && _Pred((*this)[--_Idx >>= 1], _Val)) // move _Hole up to parent
			mov(_Hole, _Idx);
		(*this)[_Hole] = _Val;    // drop _Val into final hole
		map[_Val] = _Hole;
	}
};
//template <typename _Ty, typename _Pr>
//_Pr priority_queue<_Ty, _Pr>::_Pred;
void seed_rand();
int nextInt(int max);

template<typename _Ty>
struct SubList {
	_Ty *_begin, *_end;

	struct iterator {
		_Ty *ptr;

		iterator& operator++() {
			++ptr;
			return *this;
		}

		bool operator!=(const iterator &other) const {
			return ptr != other.ptr;
		}

		_Ty& operator*() {
			return *ptr;
		}
	};

	iterator begin() {
		return {_begin};
	}

	iterator end() {
		return {_end};
	}

	_Ty& operator [](int i) {
		return _begin[i];
	}

	const _Ty& operator [](int i) const {
		return _begin[i];
	}

	int size() const {
		return _end - _begin;
	}
};

template<typename _Ty>
struct ConstSubList {
	const _Ty *_begin, *_end;

	struct iterator {
		const _Ty *ptr;

		iterator& operator++() {
			++ptr;
			return *this;
		}

		bool operator!=(const iterator &other) const {
			return ptr != other.ptr;
		}

		const _Ty& operator*() const {
			return *ptr;
		}
	};

	iterator begin() const {
		return {_begin};
	}

	iterator end() const {
		return {_end};
	}

	const _Ty& operator [](int i) const {
		return _begin[i];
	}

	int size() const {
		return _end - _begin;
	}
};

template<typename _Ty>
SubList<_Ty> subList(vector<_Ty> &list, int start) {
	int end = list.size();
	return SubList<_Ty> { list.data() + start, list.data() + end };
}

template<typename _Ty>
SubList<_Ty> subList(vector<_Ty> &list, int start, int end) {
	if (end > list.size())
		end = list.size();
	return SubList<_Ty> { list.data() + start, list.data() + end };
}

template<typename _Ty>
ConstSubList<_Ty> subList(const vector<_Ty> &list, int start, int end) {
	if (end > list.size())
		end = list.size();
	return ConstSubList<_Ty> { list.data() + start, list.data() + end };
}

template<typename _Ty>
vector<_Ty> copyOfRange(const vector<_Ty> &list, int start, int end) {
	vector<_Ty> arr(end - start);
	int index = 0;
	for (int i = start; i < end; ++i) {
		arr[index++] = list[i];
	}
	return arr;

}

template<typename _Ty>
vector<_Ty> copier(const vector<_Ty> &a, const vector<_Ty> &b) {
	vector<_Ty> c(a.size() + b.size());
	int index = 0;
	for (auto &e : a) {
		c[index++] = e;
	}
	for (auto &e : b) {
		c[index++] = e;
	}
	return c;
}

template<typename Key, typename Value>
bool operator ==(const std::map<Key, Value*> &lhs,
		const std::map<Key, Value*> &rhs) {
	if (lhs.size() != rhs.size())
		return false;
	auto q = rhs.begin();
	for (auto p : lhs) {
		if (p.first != q->first)
			return false;
		if (*p.second != *q->second)
			return false;
		++q;
	}
	return true;
}

#include <random> // std::default_random_engine

template<typename _Ty>
void shuffle(vector<_Ty> &v) {
	seed_rand();
	shuffle(v.begin(), v.end(), std::default_random_engine(rand()));
}

template<typename _Ty>
void reverse(vector<_Ty> &v) {
	std::reverse(v.begin(), v.end());
}

template<typename _Key, typename _Tp>
std::set<_Key> keys(const std::map<_Key, _Tp> &dict) {
	std::set<_Key> s;
	for (auto &entry : dict) {
		s.insert(entry.first);
	}
	return s;
}

template<typename _Key, typename _Tp>
vector<_Tp> values(const std::map<_Key, _Tp> &dict) {
	vector<_Tp> v;
	v.reserve(dict.size());
	for (auto &entry : dict) {
		v.push_back(entry.second);
	}
	return v;
}

template<typename _Key, typename _Tp>
vector<std::pair<_Key, _Tp>> items(const std::map<_Key, _Tp> &dict) {
	return vector<std::pair<_Key, _Tp>>(dict.begin(), dict.end());
}

template<typename _Ty>
_Ty sum(const vector<_Ty> &v) {
	if (!v.size())
		return _Ty();

	_Ty sum = v[0];
	auto size = v.size();
	for (size_t i = 1; i < size; ++i)
		sum += v[i];

	return sum;
}

template<typename _Ty, typename UFN>
auto sum(const vector<_Ty> &v, UFN fn) {
	decltype(fn(_Ty())) sum = 0;
	if (!v.size())
		return sum;

	for (auto &x : v)
		sum += x;

	return sum;
}

template<typename _Ty>
_Ty sum(const _Ty *begin, const _Ty *end) {
	_Ty sum = 0;

	for (auto p = begin; p != end; ++p) {
		sum += *p;
	}
	return sum;
}

template<typename _Ty>
_Ty product(const vector<_Ty> &v) {
	_Ty sum = 1;
	for (auto &x : v) {
		sum *= x;
	}
	return sum;
}

void append_file_separator(string &file);

template<typename _Ty>
std::set<_Ty> operator -(const std::set<_Ty> &lhs, const std::set<_Ty> &rhs) {
	std::set<_Ty> result;
	std::set_difference(lhs.begin(), lhs.end(), rhs.begin(), rhs.end(),
			std::inserter(result, result.begin()));
	return result;
}

template<typename _Ty>
std::set<_Ty> operator |(const std::set<_Ty> &lhs, const std::set<_Ty> &rhs) {
	std::set<_Ty> result;
	std::set_union(lhs.begin(), lhs.end(), rhs.begin(), rhs.end(),
			std::inserter(result, result.begin()));
	return result;
}

template<typename _Ty>
std::set<_Ty> operator &(const std::set<_Ty> &lhs, const std::set<_Ty> &rhs) {
	std::set<_Ty> result;
	std::set_intersection(lhs.begin(), lhs.end(), rhs.begin(), rhs.end(),
			std::inserter(result, result.begin()));
	return result;
}

#define __timer_begin() double __timer_start = clock();
#define __timer_end() std::cout << "time cost in " << __PRETTY_FUNCTION__ << " : " << (clock() - __timer_start) / CLOCKS_PER_SEC << std::endl;

template<typename _Ty, typename _Compare>
void sort(vector<_Ty> &v, _Compare __comp) {
	std::stable_sort(v.begin(), v.end(), __comp);
}

template<typename _Ty, typename _Compare>
vector<_Ty> sorted(const vector<_Ty> &v, _Compare __comp) {
	vector<_Ty> tmp = v;
	sort(tmp, __comp);
	return tmp;
}

template<typename _Ty>
void del(vector<_Ty*> &v) {
	for (auto p : v) {
		delete p;
	}
}

template<typename _Ty>
void del(vector<_Ty> &v, const vector<int> &indicesToDelete) {
    std::for_each(
		indicesToDelete.rbegin(), 
		indicesToDelete.rend(), 
		[&v](int i)
		{ 
			v.erase(v.begin() + i); 
		}
	);
}

template <typename T>
vector<T> array_splice(vector<T> &input, int start, int deleteCount=-1, const vector<T> &items = {}) {
    int len = input.size();
    // Calculate the actual start index
    if (start < 0) {
        start = len + start;
        if (start < 0) start = 0;
    }
    if (start > len)
        start = len;

    // Calculate the actual delete count
    if (deleteCount == -1)
        deleteCount = len - start;
    else if (deleteCount < 0)
		deleteCount = 0;
	else if (deleteCount > len - start)
		deleteCount = len - start;

    // Extract the removed elements (using move semantics)
    std::vector<T> removed;
    if (deleteCount > 0) {
        auto startIt = input.begin() + start;
        removed.assign(std::make_move_iterator(startIt), std::make_move_iterator(startIt + deleteCount));
    }

    // Erase the segment
    input.erase(input.begin() + start, input.begin() + start + deleteCount);

    // Insert new items
    if (!items.empty())
        input.insert(input.begin() + start, items.begin(), items.end());
    return removed;
}

template <typename T, typename P>
std::pair<std::vector<T>, std::vector<T>> array_split(const std::vector<T>& self, P pivot) {
	std::vector<T> first;
	std::vector<T> second;
    if constexpr (std::is_integral_v<P>) {
		first.assign(self.begin(), self.begin() + pivot);
		second.assign(self.begin() + pivot, self.end());
    } else {
		first.reserve(self.size());
		second.reserve(self.size());
        if constexpr (std::is_same_v<P, std::vector<int>> || std::is_same_v<P, std::vector<size_t>> || std::is_same_v<P, std::vector<long long>>) {
            std::vector<bool> bitvector(self.size(), false);
            for (const auto& i : pivot)
                bitvector[i] = true;
            for (size_t i : range(self.size())) {
                if (bitvector[i])
                    first.push_back(self[i]);
                else
                    second.push_back(self[i]);
            }
        } else {
            for (const auto& arg : self) {
                if (pivot(arg))
                    first.push_back(arg);
                else
                    second.push_back(arg);
            }
        }
    }
	return {std::move(first), std::move(second)};
}

template<typename _Key, typename _Tp>
std::map<_Key, _Tp>& operator +=(std::map<_Key, _Tp> &lhs,
		const std::map<_Key, _Tp> &rhs) {
	for (auto &tuple : rhs) {
		lhs[tuple.first] += tuple.second;
	}
	return lhs;
}

template<typename _Key, typename _Tp>
std::map<_Key, _Tp>& operator -=(std::map<_Key, _Tp> &lhs,
		const std::map<_Key, _Tp> &rhs) {
	for (auto &tuple : rhs) {
		lhs[tuple.first] -= tuple.second;
	}
	return lhs;
}

template<typename _Key>
std::set<_Key>& operator -=(std::set<_Key> &lhs,
		const std::set<_Key> &rhs) {
	for (auto &key : rhs) {
		lhs.erase(key);
	}
	return lhs;
}

string getcwd();

string now();

//#define	F_OK	0	/* Check for file existence */
//#define	X_OK	1	/* Check for execute permission. */
//#define	W_OK	2	/* Check for write permission */
//#define	R_OK	4	/* Check for read permission */
bool os_access(const std::string &name, int status = 0);

//template<typename Char>
//vector<Char> toCharArray(const std::basic_string<Char> &s) {
//	return vector<Char>(s.begin(), s.end());
//}

vector<char16_t> toCharArray(const char16_t *s, int length);

template<typename TargetType, typename SourceType>
bool instanceof(SourceType *p) {
	return dynamic_cast<TargetType*>(p);
}

template<typename TargetType, typename SourceType>
bool instanceof(const SourceType *p) {
	return dynamic_cast<const TargetType*>(p);
}

template<typename TargetType, typename SourceType>
bool instanceof(SourceType &p) {
	return dynamic_cast<TargetType*>(&p);
}

template<typename TargetType, typename SourceType>
bool instanceof(const SourceType &p) {
	return dynamic_cast<const TargetType*>(&p);
}

template<typename T>
vector<vector<T>> array_of_zeros(int m, int n) {
	vector<vector<T>> x(m);
	for (auto &v : x) {
		v.resize(n);
	}
	return x;
}

int mod(int a, int b);

int floor(int a, int b);

int ceiling(int a, int b);

vector<string> listdir(const char *dir);
vector<string> listdir(const string &dir);

template<typename _CharT>
std::basic_string<_CharT>& str_replace(
	const std::basic_string<_CharT> &search,
	const std::basic_string<_CharT> &replace,
	std::basic_string<_CharT> &subject,
	int count=0
) {
	int cnt = 0;
	if (count <= 0)
		count = subject.size();
	int start;
	while ((start = subject.find(search, start)) != std::basic_string<_CharT>::npos) {
		subject = subject.replace(start, search.size(), replace);
		start += replace.size();
		if (++cnt >= count)
			break;
	}
	return subject;
}

template<typename _CharT>
std::basic_string<_CharT>& str_replace(
	const _CharT *$old,
	const _CharT *$new,
	std::basic_string<_CharT> &subject,
	int count=0
) {
	return str_replace(std::basic_string<_CharT>($old), std::basic_string<_CharT>($new), subject, count);
}

template<typename _CharT>
std::basic_string<_CharT> getitem(const std::basic_string<_CharT> &lhs, const range &indices) {
	return lhs.substr(indices.start, indices.size());
}


// post-condition:
// return an index ∈ [0, length], which is suitable for the insertion of the value
// index < length → arr[index] ≥ value
template<typename _SourceType, typename _TargetType, typename C>
int binary_search(const vector<_SourceType> &arr, const _TargetType &value, C comparator) {
	int begin = 0, end = arr.size();
	for (;;) {
		int mid = (begin + end) >> 1;
		if (begin == end)
			return mid;
		int ret = comparator(arr[mid], value);
		if (ret < 0)
			begin = mid + 1;
		else if (ret > 0)
			end = mid;
		else
			return mid;
	}
}

template<typename _Ty>
int binary_search(const vector<_Ty> &arr, const _Ty &value) {
	return binary_search(arr, value, [] (auto &lhs, auto &rhs) {
		return lhs - rhs;
	});
}

template<typename _Ty>
_Ty pop_back(vector<_Ty> &arr) {
	auto back = arr.back();
	arr.pop_back();
	return back;
}

template<typename _Ty>
std::set<_Ty> as_set(std::initializer_list<_Ty> list) {
	std::set<_Ty> s;
	for (const auto &x : list) {
		s.insert(x);
	}
	return s;
}

template<typename _Ty>
std::set<_Ty> as_set(const vector<_Ty> &v) {
	return std::set<_Ty>(v.begin(), v.end());
}

template<typename _Ty>
std::set<_Ty> as_set(const ConstSubList<_Ty> &v) {
	return std::set<_Ty>(v.begin(), v.end());
}

template<typename _Ty>
std::set<_Ty> as_set(const SubList<_Ty> &v) {
	return std::set<_Ty>(v.begin(), v.end());
}

template<typename _Key>
std::set<_Key>& operator -=(std::set<_Key> &lhs,
		const std::initializer_list<_Key> &rhs) {
	return lhs -= as_set(rhs);
}

template<typename _Container>
int len(const _Container &x) {
	return x.size();
}

std::string json_encode(std::string s);

#include <bitset>
std::string bin(int n);
std::string hex(int n);
std::string hex(char n);

// https://en.wikipedia.org/wiki/Steinhaus%E2%80%93Johnson%E2%80%93Trotter_algorithm#Recursive_structure
void generate_permutations(int n, std::function<void(const vector<int> &)> fn);