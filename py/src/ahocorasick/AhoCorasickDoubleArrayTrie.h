#pragma once
/**
 * An implementation of Aho Corasick algorithm based on Double Array Trie
 *
 * @author hankcs
 */
#include "../std/utility.h"
#include <vector>
#include <math.h>

#include "../std/TextTreeNode.h"
using std::vector;

#include <iostream>
using std::cout;
using std::endl;

#include <stack>
#include <queue>

#include "KeyGenerator.h"

template<typename _CharT, typename V>
struct AhoCorasickDoubleArrayTrie {
	using String = std::basic_string<_CharT>;

	struct Node {
		Node() :
				base(0), check(0), failure(-1) {
		}

		int base;
		int check;

		/**
		 * emission table of the Aho Corasick automata
		 */
		vector<int> emit;

		/**
		 * fail table of the Aho Corasick automata
		 */
		int failure = -1;

		void clear() {
			base = check = 0;
			emit.clear();
			failure = -1;
		}

		friend std::ostream &operator << (std::ostream &ostr, const Node &obj){
			return ostr << "base = " << obj.base <<
					", check = " << obj.check <<
					", failure = " << obj.failure <<
					", emit = " << obj.emit << endl;
		}
	};

	String toString() const {
		return root->toString();
	}

	friend std::ostream& operator <<(std::ostream &cout,
			const AhoCorasickDoubleArrayTrie &p) {
		return cout << p.toString();
	}

	vector<Node> node;

	vector<int> getBase(){
		vector<int> base(node.size());
		for (int i = 0; i < base.size(); ++i){
			base[i] = node[i].base;
		}

		return base;
	}

	vector<int> getCheck(){
		vector<int> check(node.size());
		for (int i = 0; i < check.size(); ++i){
			check[i] = node[i].check;
		}

		return check;
	}

	vector<int> getFailure(){
		vector<int> failure(node.size());
		for (int i = 0; i < failure.size(); ++i){
			failure[i] = node[i].failure;
		}

		return failure;
	}

	vector<V> getValues(){
		vector<V> values(emit.size());
		for (int i = 0; i < emit.size(); ++i){
			values[i] = emit[i].value;
		}

		return values;
	}

	vector<int> getCharLength(){
		vector<int> charLength(emit.size());
		for (int i = 0; i < emit.size(); ++i){
			charLength[i] = emit[i].char_length;
		}

		return charLength;
	}

	vector<vector<int>> getEmit(){
		vector<vector<int>> emit(node.size());
		for (int i = 0; i < emit.size(); ++i){
			emit[i] = node[i].emit;
		}

		return emit;
	}

	struct Emit {
		/**
		 * the length of every key
		 */
		int char_length;

		/**
		 * outer value
		 */
		V value;

		friend std::ostream& operator <<(std::ostream &cout, const Emit &p) {
			return cout << "(" << p.char_length << ", " << p.value << ")"
					<< endl;
		}
	};

	vector<Emit> emit;

	struct Hit {
		/**
		 * the beginning index, inclusive.
		 * * the ending index, exclusive.
		 */
		int begin, end;
		/**
		 * the value assigned to the keyword
		 */
		V value;

		bool is_null() const {
			return begin == end;
		}

		bool operator ==(const Hit &obj) const {
			return begin == obj.begin && end == obj.end && value == obj.value;
		}

		friend std::ostream& operator <<(std::ostream &cout, const Hit &p) {
			return std::cout << "["<< p.begin << ":" << p.end << "] = " << p.value;
		}

		String substr(const String &text) const {
			return text.substr(begin, end - begin);
		}

		bool intersects(const Hit &part) const {
			return begin < part.end && part.begin < end;
		}

		bool intersects(const Hit *part) const {
			return begin < part->end && part->begin < end;
		}

		bool intersects(const vector<Hit> &part) const {
			for (auto &hit: part){
				if (intersects(hit))
					return true;
			}

			return false;
		}

		bool intersects(const vector<Hit*> &part) const {
			for (auto hit: part){
				if (intersects(*hit))
					return true;
			}

			return false;
		}
	};

	struct HitIndexed: Hit {
		HitIndexed() {
		}

		HitIndexed(const Hit &hit, AhoCorasickDoubleArrayTrie *self, int index) :
				Hit(hit), self(self), index(index) {
		}

		AhoCorasickDoubleArrayTrie *self;
		int index;
		void setValue(const V &value) {
			this->value = value;
			self->emit[index].value = value;
		}
	};

	/**
	 * Parse text
	 *
	 * @param text The text
	 * @return a list of outputs
	 */
	vector<Hit> parseText(const String &text) {
//		Timer timer(__PRETTY_FUNCTION__);
		int position = 0;
		int currentState = 0;
		vector<Hit> collectedEmits;
		for (auto ch : text) {
			currentState = getState(currentState, ch);
			storeEmits(++position, currentState, collectedEmits);
		}

		return collectedEmits;
	}

	vector<HitIndexed> parseTextIndexed(const String &text) {
		int position = 0;
		int currentState = 0;
		vector<HitIndexed> collectedEmits;
		for (auto ch : text) {
			currentState = getState(currentState, ch);
			storeEmits(++position, currentState, collectedEmits);
		}
		return collectedEmits;
	}

	vector<Hit> parseTextReturnLongest(const String &text) {
		int position = 0;
		int currentState = 0;
		vector<Hit> collectedEmits;
		for (auto ch : text) {
			currentState = getState(currentState, ch);
			auto hit = storeEmits(++position, currentState);
			if (!hit.is_null())
				collectedEmits.push_back(hit);
		}

		return collectedEmits;
	}

	/**
	 * Checks that string contains at least one substring
	 *
	 * @param text source text to check
	 * @return {@code true} if string contains at least one substring
	 */
	bool matches(const String &text) {
		int currentState = 0;
		for (auto ch : text) {
			currentState = getState(currentState, ch);
			if (node[currentState].emit.size()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Get value by a String key, just like a map.get() method
	 *
	 * @param key The key
	 * @return value if exist otherwise it return nullptr
	 */
	V& get(const String &key) {
		int index = exactMatchSearch(key);
		if (index >= 0) {
			return emit[index].value;
		}
		static V null;
		return null;
	}

	/**
	 * Pick the value by index in value array <br>
	 * Notice that to be more efficiently, this method DO NOT check the parameter
	 *
	 * @param index The index
	 * @return The value
	 */
	V& get(int index) {
		return emit[index].value;
	}

	/**
	 * A result output
	 *
	 */
	/**
	 * transmit state, supports failure function
	 *
	 * @param currentState
	 * @param character
	 * @return
	 */
	int getState(int currentState, int character) { // @suppress("No return")
		for (;;) {
			int newCurrentState = nextState(currentState, character);
			if (newCurrentState != -1)
				return newCurrentState;
			currentState = node[currentState].failure;
		}
	}

	/**
	 * store output
	 *
	 * @param position
	 * @param currentState
	 * @param collectedEmits
	 */
	void storeEmits(int position, int currentState,
			vector<Hit> &collectedEmits) {
		for (int hit : node[currentState].emit) {
			collectedEmits.push_back( { position - emit[hit].char_length,
					position, emit[hit].value });
		}
	}

	void storeEmits(int position, int currentState,
			vector<HitIndexed> &collectedEmits) {

		for (int hit : node[currentState].emit) {
			collectedEmits.push_back(
					HitIndexed( { position - emit[hit].char_length, position,
							emit[hit].value }, this, hit));
		}
	}

	Hit storeEmits(int position, int currentState) {
		vector<int> &hitArray = node[currentState].emit;
		if (hitArray.size()) {
			int hit = hitArray.back();
			return {position - emit[hit].char_length, position,
				emit[hit].value};
		}
		static Hit null = { 0, 0, V() };
		return null;
	}

	/**
	 * transition of a state
	 *
	 * @param current
	 * @param c
	 * @return
	 */
	int transition(int current, _CharT c) {
		int b = current;
		int p;

		p = b + (_CharT) (c + 1);
		if (b == node[p].check)
			b = node[p].base;
		else
			return -1;

		p = b;
		return p;
	}

	/**
	 * transition of a state, if the state is root and it failed, then returns the
	 * root
	 *
	 * @param nodePos
	 * @param c
	 * @return
	 */
	int nextState(int nodePos, int c) {
		int b = node[nodePos].base;
		int p;

		p = b + c + 1;
		if (b != (p < (int) node.size() ? node[p].check : 0)) {
			if (nodePos == 0) // depth == 0
				return 0;
			return -1;
		}

		return p;
	}

	/**
	 * match exactly by a key
	 *
	 * @param key the key
	 * @return the index of the key, you can use it as a perfect hash function
	 */
	int exactMatchSearch(const String &key) {
		return exactMatchSearch(key, 0, 0, 0);
	}

	/**
	 * match exactly by a key
	 *
	 * @param key
	 * @param pos
	 * @param len
	 * @param nodePos
	 * @return
	 */
	int exactMatchSearch(const String &key, int pos, int len, int nodePos) {
		if (len <= 0)
			len = key.size();
		if (nodePos <= 0)
			nodePos = 0;

		int result = -1;

		return getMatched(pos, len, result, key, node[nodePos].base);
	}

	int getMatched(int pos, int len, int result, const String &keyChars,
			int b1) {
		int b = b1;
		int p;

		for (int i = pos; i < len; i++) {
			p = b + (_CharT) (keyChars[i] + 1);
			if (b == node[p].check)
				b = node[p].base;
			else
				return result;
		}

		p = b; // transition through '\0' to check if it's the end of a word
		int n = node[p].base;
		if (b == node[p].check) { // yes, it is.
			result = -n - 1;
		}
		return result;
	}

	/**
	 * match exactly by a key
	 *
	 * @param keyChars the _CharT array of the key
	 * @param pos      the begin index of _CharT array
	 * @param len      the length of the key
	 * @param nodePos  the starting position of the node for searching
	 * @return the value index of the key, minus indicates nullptr
	 */
	int exactMatchSearch(const _CharT *keyChars, int pos, int len,
			int nodePos) {
		int result = -1;

		return getMatched(pos, len, result, keyChars, node[nodePos].base);
	}

	/**
	 * @return the size of the keywords
	 */
	int memory_size() {
		int length = 0;
		for (int i = node.size() - 1; i >= 0; --i) {
			if (node[i].check != 0) {
				length = i + 1;
				break;
			}
		}
		return length;
	}

	struct State;

	struct Transition {
		int character;
		State *parent;

		State* node();
		void set_failure();
	};

	vector<String> getKeys(){
		auto dict = enumerate();
		int size = dict.size();
		vector<String> keys(size);
		int i = 0;
		for (auto &entry: dict){
			keys[i++] = entry.first;
		}
		return keys;
	}

	std::map<String, V> enumerate() {
		std::map<String, V> map;
		root->enumerate(String(), map);
		return map;
	}

	struct State {

		AhoCorasickDoubleArrayTrie *self;
		State *failure;
		std::map<int, State*> success;
		int index;

		void enumerate(const String &text, std::map<String, V> &map) {
			for (auto &entry : success) {
				if (entry.first < 0) {
					int index = emit().back();
					//::print("index =", index);
					map[text] = self->emit[index].value;
				} else {
					entry.second->enumerate(text + (_CharT) entry.first, map);
				}
			}
		}

		~State() {
			for (auto &entry : success) {
				delete entry.second;
			}
		}

		vector<int>& emit() {
			return self->node[index].emit;
		}

		const vector<int>& emit() const {
			return self->node[index].emit;
		}

		void emit(int emit) {
			self->node[index].base = -emit - 1;
			assert_neq(self->node[index].check, 0);
		}

		int try_base() {
			for (int begin : self->used) {
				assert_false(self->used.isRegistered(begin));
				if (try_update_base(begin)) {
					return begin;
				}
			}

			return -1;
		}

		int update_base() {
			int begin = self->node[index].base;
			assert_or(self->used.isRegistered(begin), begin == 0);

			int _begin = try_base();
			self->node[index].base = _begin;
			assert_neq(self->node[index].check, 0);
			ensureCapacity();

			for (auto &entry : success) {
				int word = entry.first;
				auto state = entry.second;
				if (state->index != 0) {
					assert_eq(state->index, begin + (_CharT ) (word + 1));
					assert_eq(self->node[state->index].check, begin);
				}

				int code = _begin + (_CharT) (word + 1);
				assert_eq(self->node[code].check, 0);
				if (state->index != 0) {
					self->node[code].base = self->node[state->index].base;
					self->node[code].emit = self->node[state->index].emit;

					self->node[state->index].clear();
				}
				state->index = code;

				self->node[code].check = _begin;
			}

			self->occupy(_begin);
			self->recycle(begin);

			return _begin;
		}

		bool operator !=(const State &obj) const {
			return !(*this == obj);
		}

		bool operator ==(const State &obj) const {
//			if (depth != obj.depth)
//				return false;

			if (success != obj.success)
				return false;

			if (failure == nullptr) {
				if (obj.failure != nullptr)
					return false;
			} else {
				if (obj.failure == nullptr)
					return false;
				if (failure->depth() != obj.failure->depth())
					return false;
			}

			if (toTreeMap() != obj.toTreeMap())
				return false;

			return true;
		}

		std::map<int, V> toTreeMap() const {
			std::map<int, V> map;
			for (auto &entry : self->toTreeMap(this->emit())) {
				map[entry.first] = self->emit[entry.second].value;
			}
			return map;
		}

		bool update_failure(State *parent, _CharT ch) {
			auto newFailureState = self->newFailureState(parent, ch);
			if (failure == newFailureState) {
				return false;
			}

			setFailure(newFailureState);
			addEmit(newFailureState->emit());
			return true;
		}

		State* update_failure(State *parent, _CharT ch, State *keywordNode) {
			auto newFailureState = self->newFailureState(parent, ch);
			if (failure == newFailureState) {
				if (keywordNode != nullptr)
					addEmit(keywordNode->emit());
				return failure;
			}

			setFailure(newFailureState);
			addEmit(newFailureState->emit());
			return nullptr;
		}

		void constructFailureStates_(State *parent, State *rootState,
				const String &keyword) {
			_CharT character = keyword[0];
			rootState = rootState->success[(int) character];

			if (failure->depth() <= rootState->depth()) {
				setFailure(rootState);
			}

			addEmit(rootState->emit());

			// Second, determine the fail state for all depth > 1 state
			if (keyword.size() > 1) {
//				State *state = success[(int) keyword[0]];
//				if (state != nullptr) {
//					state->constructFailureStates_(this, rootState, keyword);
//				}
				auto find = success.find((int) keyword[1]);
				if (find != success.end()) {
					find->second->constructFailureStates_(this, rootState,
							keyword.substr(1));
				}
			}
		}

		void constructFailureStates(State *parent, State *rootState,
				const String &keyword) {
			_CharT character = keyword[0];
			rootState = rootState->success[(int) character];

			bool failure = true;
			if (!update_failure(parent, character)) {
				parent = update_failure(parent, character, rootState);
				failure = false;
			}

			// Second, determine the fail state for all depth > 1 state

			if (keyword.size() > 1) {
//				State *state = success[(int) keyword[0]];
//				if (state != nullptr) {
//					if (failure)
//						state->constructFailureStates(this, rootState, keyword);
//					else {
//						state->constructFailureStates_(this, rootState,
//								keyword);
//					}
//				}

				auto find = success.find((int) keyword[1]);
				if (find != success.end()) {
					auto state = find->second;
					auto _keyword = keyword.substr(1);
					if (failure)
						state->constructFailureStates(this, rootState,
								_keyword);
					else {
						state->constructFailureStates_(this, rootState,
								_keyword);
					}
				}
			}
		}

		void checkValidity() {
			this->checkValidity(false);
		}

		void checkValidity(bool recursively) {
			if (emit().size()) {
				for (size_t i = 1; i < emit().size(); ++i) {
					assert_lt(self->emit[emit()[i - 1]].char_length,
							self->emit[emit()[i]].char_length);
				}
			}

			if (failure != nullptr) {
				assert_eq(self->node[index].failure, failure->index);
				assert_false(failure->is_null_terminator());

			} else {
				assert_eq(self->node[index].failure, -1);
			}

			assert_eq(self->node[index].emit, emit());
/*
			int begin = self->node[index].base;
			for (auto &entry : success) {
				assert_eq(self->node[begin + (_CharT ) (entry.first + 1)].check,
						begin);
			}
*/
			for (auto &entry : success) {
				auto state = entry.second;
				if (state->is_null_terminator()) {
					assert_eq(
							-self->node[begin + (_CharT ) (entry.first + 1)].base
									- 1, emit().back());
				}
			}

			if (recursively)
				for (auto &entry : this->success) {
					entry.second->checkValidity(recursively);
				}
		}

		void removeIndex(int index) {
			int last = self->emit.size() - 1;
			if (emit().size()) {
				int first_index = indexOf(emit(), index);
				int last_index = indexOf(emit(), last);
				bool needMofification = false;
				if (last_index >= 0) {
					emit()[last_index] = index;
					needMofification = true;
				}

				if (first_index >= 0) {
					emit() = concatExcept(emit(), first_index);
					needMofification = false;
				}
				if (needMofification) {
					emit() = toArray(self->toTreeMap(emit()));
				}
			}

			for (auto &entry : success) {
				entry.second->removeIndex(index);
			}
		}

		int depth() {
			if (this->success.size() == 1 && this->success.count(-1)) {
				assert_true(self->emit.size());
				return lastKey();
			}

			assert_false(this->success.empty());
			return this->success.rbegin()->second->depth() - 1;
		}

		int lastKey() {
			return self->emit[emit().back()].char_length;
		}

		int lastValue() {
			return emit().back();
		}

		int remove(int char_length) {
//			emit.remove(char_length);
			auto map = self->toTreeMap(emit());
			if (map.count(char_length)) {
				int index = map[char_length];
				map.erase(char_length);
				emit() = toArray(map);
				return index;
			}
			return -1;
		}

		bool containsKey(int char_length) {
			return self->toTreeMap(emit()).count(char_length);
		}

		bool delete_failure(State *parent, _CharT ch) {
			auto newFailureState = self->newFailureState(parent, ch);
			if (failure == newFailureState) {
				return false;
			}

			setFailure(newFailureState);
			return true;
		}

		void deleteFailureStates(State *parent, const String &keyword,
				int char_length) {
			delete_failure(parent, keyword[0]);

			if (keyword.size() == 1) {
				remove(char_length);
			} else {
				auto find = success.find((int) keyword[1]);
				if (find != success.end()) {
					find->second->deleteFailureStates(this, keyword.substr(1),
							char_length);
				}
			}
		}

		int deleteEmit(std::stack<State*> &parent) {
			auto leaf = success[-1];
			success.erase(-1);
			assert_eq(self->node[leaf->index].check, leaf->index);
			self->node[leaf->index].clear();

			if (is_null_terminator()) {
				State *orphan = this;

				while (!parent.empty()) {
					self->recycle(self->node[orphan->index].base);
					self->node[orphan->index].clear();

					auto father = parent.top();

					int unicode = -1;
					for (auto &entry : father->success) {
						if (entry.second == orphan) {
							unicode = entry.first;
							break;
						}
					}
					father->success.erase(unicode);
					parent.pop();

					if (father->is_null_terminator()) {
						orphan = father;
					} else
						return unicode;
				}
			}

//			parent.push_back(this);
			return -1;
		}

		void print() {
			int begin = node[index].base;
			for (auto &entry : success) {
				cout << "check[" << (begin + (_CharT) (entry.first + 1))
						<< "] = ";

				assert_eq(node[begin + (_CharT ) (entry.first + 1)].check,
						begin);
			}

			cout << "base[" << index << "] = " << begin;

			for (auto &entry : success) {
				auto state = entry.second;
				if (state->is_null_terminator()) {
					cout << ", \tbase[" << (begin + (_CharT) (entry.first + 1))
							<< "] = value["
							<< (-node[begin + (_CharT) (entry.first + 1)].base
									- 1) << "] = "
							<< self->emit[emit().back()].value;

					assert_eq(
							-node[begin + (_CharT ) (entry.first + 1)].base - 1,
							emit().back());
				}
			}
			cout << endl;
		}

		int size() {
			int size = 1;
			for (auto &entry : success) {
				size += entry.second->size();
			}
			return size;
		}

		void appendNullTerminator(int index) {
			auto null_terminator = new State { self, nullptr, { }, 0 };
			null_terminator->index = -index - 1;
			success[-1] = null_terminator;
		}

		void ensureCapacity() {
			int begin = self->node[index].base;
			int addr = begin + (_CharT) (this->success.rbegin()->first + 1);
			if (addr >= (int) self->node.size()) {
				self->resize(addr + 1);
			}
		}

		int try_nextCheckPos(int begin) {
			assert_gt(begin, 0);
			int addr = begin + (_CharT) (success.begin()->first + 1);
			if (addr < (int) self->node.size() && self->node[addr].check != 0) {
				return -1;
			}
			return addr;
		}

		int try_nextCheckPos() {
			int begin = std::max(1,
					self->nextCheckPos - (_CharT) (success.begin()->first + 1));

			while (true) {
				self->nextCheckPos = try_nextCheckPos(begin);
				if (self->nextCheckPos > 0)
					return begin;
				++begin;
			}
		}

		int try_base_with_optimal_start_point() {
			int start = try_nextCheckPos() - 1;
			vector<int> improbableKeys;

			for (int begin : self->used.tailSet(start)) {
				assert_and(begin > start, !self->used.isRegistered(begin));
				if (try_update_base(begin)){
                    for (int key : improbableKeys) {
                        self->used.register_key(key);
                        self->keysSearchFailures.erase(key);
                    }

					return begin;
				}

                int &failureCount = self->keysSearchFailures[begin];
				++failureCount;
				//too many failures indicate this key has no value to be tried?
				if (failureCount > 128)
					improbableKeys.push_back(begin);
			}

			return -1;
		}

		bool try_update_base(int begin) {
			assert_gt(begin, 0);
			for (auto &entry : success) {
				int word = entry.first;
				int addr = begin + (_CharT) (word + 1);
				if (addr < (int) self->node.size()
						&& self->node[addr].check != 0) {
					return false;
				}
			}
			return true;
		}

		bool is_null_terminator() {
			return success.empty();
		}

		State* addState(int character, vector<Transition> &queue) {
			auto nextState = success[character];
			if (nextState == nullptr) {
				nextState = new State { self, nullptr, { }, 0 };
				success[character] = nextState;
				queue.push_back(Transition { character, this });
			}
			return nextState;
		}

		/**
		 * insert the siblings to double array trie
		 *
		 * @param siblings the siblings being inserted
		 * @return the position to insert them
		 */
		void insert() {
			if (is_null_terminator())
				return;
			int begin = try_base_with_optimal_start_point();
			self->occupy(begin);
			self->node[index].base = begin;

			ensureCapacity();
			for (auto &entry : success) {
				auto state = entry.second;
				int index = begin + (_CharT) (entry.first + 1);
				if (state->is_null_terminator()) {
					self->node[index].base = state->index;
					state->index = index;
				} else {
					if (state->index < 0) {
						int emit = -state->index - 1;
						state->index = index;
						state->emit() = vector<int> { emit };
					} else {
						state->index = index;
					}
				}

				self->node[index].check = begin;
			}

			for (auto &entry : success) {
				entry.second->insert();
			}
		}

		void addEmit() {
			auto leaf = new State { self, nullptr, { }, 0 };
			success[-1] = leaf;
			if (success.size() > 1) {
				int begin = self->node[index].base;
				if (self->node[begin].check == 0) {
					self->node[begin].check = begin;
					assert_true(self->used.isRegistered(begin));

					for (auto &entry : success) {
						if (entry.first == -1)
							continue;
						entry.second->checkValidity();
					}

				} else {
					begin = this->try_base();
					assert_false(self->used.isRegistered(begin));

					assert_true(
							self->used.isRegistered(self->node[index].base));
					self->recycle(self->node[index].base);

					assert_eq(self->node[begin].check, 0);
					self->node[begin].check = self->node[index].base = begin;

					assert_neq(self->node[index].check, 0);

					for (auto &entry : success) {
						if (entry.first == -1)
							continue;

						int code = begin + (_CharT) (entry.first + 1);
						auto state = entry.second;
						assert_and(self->node[code].check == 0,
								self->node[code].base == 0);

						self->node[code].check = begin;
						self->node[code].base = self->node[state->index].base;
						self->node[code].emit = self->node[state->index].emit;

						if (state->index != begin)
							self->node[state->index].clear();

						state->index = code;
						state->checkValidity();
					}
					self->occupy(begin);
				}

				leaf->index = begin;
				leaf->emit(self->emit.size() - 1);
			}
		}

		void addEmit(int value_index) {
			std::map<int, int> map = self->toTreeMap(emit());
			map[self->emit[value_index].char_length] = value_index;
			emit() = toArray(map);
		}

		void check_initialization() {
			assert_le(index, 0);
			if (index < 0) {
				assert_lt(-index - 1, (int )self->emit.size());
			}

			for (auto &entry : success) {
				entry.second->check_initialization();
			}
		}

		void initializeEmit(int value_index) {
			index = -value_index - 1;
		}

		void addEmit(const vector<int> &emit) {
			auto map = self->toTreeMap(this->emit());
			auto _map = self->toTreeMap(emit);
			map.insert(_map.begin(), _map.end());
			this->emit() = toArray(map);
		}

		void setFailure(State *failure) {
			this->failure = failure;
			self->node[index].failure = failure->index;
		}

		bool isRoot() const {
//			return index == 0;
			if (index == 0) {
				assert_eq(this, self->root);
				return true;
			}
			return false;

		}

		void locate_state(int ch, vector<State*> &list, int depth) {
			++depth;
			for (auto &entry : success) {
				if (entry.first == -1)
					continue;

				auto state = entry.second;
				assert_eq(state->depth(), depth);
				if (entry.first == ch && depth > 1) {
					list.push_back(this);
				}
				state->locate_state(ch, list, depth);
			}
		}

		vector<State*> locate_state(int ch) {
			vector<State*> list;
			locate_state(ch, list, 0);
			return list;
		}

		vector<State*> locate_state(const String &keyword) {
			vector<State*> list;
			locate_state(String(), keyword, list, 0);
			return list;
		}

		void locate_state(const String &prefix, const String &keyword,
				vector<State*> &list, int depth) {
			++depth;
			for (auto &entry : success) {
				if (entry.first == -1)
					continue;
				auto state = entry.second;
				String newPrefix = prefix + (_CharT) (int) entry.first;

				assert_eq(state->depth(), depth);

				if (newPrefix == keyword && depth > (int) keyword.size()) {
					list.push_back(this);
				}

				for (;;) {
					if (startsWith(keyword, newPrefix)
							&& newPrefix.size() < keyword.size()) {
						state->locate_state(newPrefix, keyword, list, depth);
						break;
					}

					if (newPrefix.empty())
						break;
					newPrefix = newPrefix.substr(1);
				}
			}
		}

		State* nextState(int character) const {
			auto find = success.find(character);
			if (find == success.end()) {
				return isRoot() ? (State*) this : nullptr;
			}
			return find->second;
		}

		State* addState(int character) {
			auto nextState = success[character];
			if (nextState == nullptr) {
				nextState = new State { self, nullptr, { }, 0 };
				success[character] = nextState;
			}
			return nextState;
		}

		TextTreeNode<_CharT>* toShadowTree() {
			String value(1, '@');

			if (self->node[this->index].base > 0)
				value += std::toString(this->index) + String(1, ':')
						+ std::toString(self->node[this->index].base);
			else
				value += std::toString(this->index) + String(1, '=')
						+ std::toString(-self->node[this->index].base - 1);

			auto newNode = new TextTreeNode<_CharT>(value);
			vector<int> list(success.size());

			size_t i = 0;
			for (auto &entry : success) {
				list[i++] = entry.first;
			}

			vector<TextTreeNode<_CharT>*> arr(list.size());
			for (i = 0; i < arr.size(); ++i) {
				int word = list[i];
				auto state = success[word];
				auto node = state->toShadowTree();

				if (word == -1)
					value = String(1, '*');
				else
					value = String(1, word);

//				if (state->failure != nullptr && state->failure.depth != 0) {
//					node.value += String.valueOf(state->failure.depth);
//				}
//				if (state->is_null_terminator()) {
//					newNode.value += '+';
//				} else {
				node->value = value + node->value;
				arr[i] = node;
//				}
			}

			if (arr.size()) {
				int x_length = arr.size() / 2;
				int y_length = arr.size() - x_length;

// tree node
				if (x_length > 0) {
					newNode->x.resize(x_length);
					std::copy(arr.begin(), arr.begin() + x_length,
							newNode->x.begin());
				}

				if (y_length > 0) {
					newNode->y.resize(y_length);
					std::copy(arr.begin() + x_length, arr.end(),
							newNode->y.begin());
				}
			}
			return newNode;
		}

		String toString() {
			object<TextTreeNode<_CharT>> root = this->toShadowTree();
			return root->toString(root->max_width() + 1, true);
//			return root->toString(root->max_width() + 1);
		}
	};

	/**
	 * the root state of trie
	 */
	object<State> root;
	/**
	 * whether the position has been used
	 */
	KeyGenerator used;

	std::unordered_map<int, int> keysSearchFailures;
	/**
	 * the next position to check unused memory
	 */
	int nextCheckPos = 0;

	/**
	 * Build from a map
	 *
	 * @param map a map containing key-value pairs
	 */
	AhoCorasickDoubleArrayTrie(const std::map<String, V> &map) :
			emit(map.size()) {
		Timer timer(__PRETTY_FUNCTION__);
		root = new State { this, nullptr, { }, 0 };
		int value_index = 0;
		for (auto &entry : map) {
			const String &keyword = entry.first;
			State *currentState = this->root;
			for (_CharT character : keyword) {
				currentState = currentState->addState(character);
			}

			emit[value_index] = { (int) keyword.size(), entry.second };
			currentState->initializeEmit(value_index);
			currentState->appendNullTerminator(value_index);

			++value_index;
		}

		root->check_initialization();
		resize(65536);
		root->insert();

//		used = nullptr;

		int length = memory_size();
		if (length < (int) node.size()) {
			node.resize(length);
		}

		constructFailureStates();
	}

	/**
	 * construct failure table
	 */
	void constructFailureStates() {
		std::queue<State*> queue;

// First, set the fail state of all depth 1 states to the root state
		for (auto &entry : root->success) {
			auto depthOneState = entry.second;
			depthOneState->setFailure(root);
			queue.push(depthOneState);
		}

// Second, determine the fail state for all depth > 1 state
		while (!queue.empty()) {
			auto currentState = queue.front();
			queue.pop();

			for (auto &entry : currentState->success) {
				int transition = entry.first;
				if (transition == -1)
					continue;

				auto targetState = entry.second;
				queue.push(targetState);

				auto newFailureState = this->newFailureState(currentState,
						transition);
				targetState->setFailure(newFailureState);
				targetState->addEmit(newFailureState->emit());
			}
		}

//		root = nullptr;
	}

	/**
	 * allocate the memory of the dynamic array
	 *
	 * @param newSize of the new array
	 */
	void resize(int newSize) {
		assert_or(node.empty(), newSize > (int )node.size());
		newSize = (int) std::pow(2.0, (int) ceil(log(newSize) / log(2.0)));

		vector<Node> _pointer(newSize);

		int start;
		if (node.size()) {
			std::copy(node.begin(), node.end(), _pointer.begin());
			start = node.size();
		} else
			start = 0;

		for (int i = start; i < newSize; ++i) {
			_pointer[i] = Node();
		}

		node = _pointer;
	}

	int try_base(std::map<int, State*> &siblings) {
		int begin = 0;
		int pos = std::max((_CharT) (siblings.begin()->first + 1) + 1,
				nextCheckPos) - 1;
//		int nonzero_num = 0;
		int first = 0;

		outer: while (true) {
			pos++;

			if (node[pos].check != 0) {
//				nonzero_num++;
				continue;
			}

			if (first == 0) {
				nextCheckPos = pos;
				first = 1;
			}

			begin = pos - (_CharT) (siblings.firstKey() + 1); // 当前位置离第一个兄弟节点的距离
//			if (pointer.size() <= (begin + (_CharT) (siblings.lastKey() + 1))) {
//				// progress can be zero // 防止progress产生除零错误
//				double l = (1.05 > 1.0 * v.size() / (progress + 1)) ? 1.05 : 1.0 * v.size() / (progress + 1);
//				resize((int) (pointer.size() * l));
//			}

			if (used.isRegistered(begin))
				continue;

			auto iterator = siblings.iterator();

			if (iterator.hasNext()) {
				iterator.next();
				while (iterator.hasNext()) {
					auto p = iterator.next();
					int addr = begin + (_CharT) (p.first + 1);
					if (addr < node.size() && node[addr].check != 0)
						goto outer;
				}
			}

			break;
		}

// -- Simple heuristics --
// if the percentage of non-empty contents in check between the index
// 'next_check_pos' and 'check' is greater than some constant value (e.g.
// 0.9),new 'next_check_pos' index is written by 'check'.
//		if (1.0 * nonzero_num / (pos - nextCheckPos + 1) >= 0.95)
//			nextCheckPos = pos; // 从位置 next_check_pos 开始到 pos 间，如果已占用的空间在95%以上，下次插入节点时，直接从 pos 位置处开始查找

		return begin;
	}

	void occupy(int begin) {
//		System.out.println("occupy begin = " + begin);
		assert_false(used.isRegistered(begin));
		used.register_key(begin);
	}

	void recycle(int begin) {
		if (begin > 0) {
			assert_true(used.isRegistered(begin));
			used.unregister_key(begin);
		}
	}

	vector<int> getNonzeroCheckIndex() {
		vector<int> indices;
		for (size_t i = 0; i < node.size(); ++i) {
			if (node[i].check != 0) {
				indices.push_back(i);
			}
		}
		return indices;
	}

	vector<int> getNonzeroBaseIndex() {
		vector<int> indices;
		for (size_t i = 0; i < node.size(); ++i) {
			if (node[i].base != 0) {
				indices.push_back(i);
			}
		}

		return indices;
	}

	vector<int> getValidUsedIndex() {
		vector<int> indices;
		for (size_t i = 1; i < node.size(); ++i) {
			if (!used.isRegistered(i))
				continue;

			indices.push_back(i);
		}

		return indices;
	}

	void checkValidity() {
		root->checkValidity(true);
		for (auto &node : this->node) {
			if (node.check != 0) {
				assert_neq(node.base, 0);
			} else {
				assert_true(node.emit.empty());
				assert_eq(node.failure, -1);
			}
		}

		auto checkIndex = getNonzeroCheckIndex();
		auto baseIndex = getNonzeroBaseIndex();

		assert_eq(checkIndex.size() + 1, baseIndex.size());

		assert_eq(baseIndex[0], 0);

		assert_eq(vector<int>(baseIndex.begin() + 1, baseIndex.end()),
				checkIndex);

		auto usedIndex = getValidUsedIndex();
		assert_eq(usedIndex.size() + emit.size(), baseIndex.size());

		assert_eq(this->root->size(), (int )baseIndex.size());
/*
		for (int kinder : checkIndex) {
			assert_true(used.isRegistered(node[kinder].check));
		}*/

		for (int index : baseIndex) {
			int begin = node[index].base;
			if (begin < 0) {
				assert_lt(-begin - 1, (int )emit.size());
			} else {
				assert_true(used.isRegistered(begin));
			}
		}

		for (int begin : usedIndex) {
			if (node[begin].check != 0) {
				if (node[begin].check == begin) {
					assert_lt(node[begin].base, 0);
				} else {
					assert_gt(node[begin].base, 0);
				}
			}
		}

		assert_eq((int )baseIndex.size(), this->root->size());
		assert_eq(usedIndex.size() + emit.size(), baseIndex.size());
	}

//	order > 0 means ascending order
//	order < 0 means descending order
//	order = 0 means random order	
	int order;

	void remove(const String &keyword) {
		State *currentState;
		if (order < 0) {
		} else {
			int index = exactMatchSearch(keyword);
			if (index < 0)
				return;
//			int length = emit.size();
// now change emit from key.size() to index
			removeIndex(index);

			currentState = this->root;
			std::stack<State*> parent;
			for (auto ch : keyword) {
				parent.push(currentState);
				currentState = currentState->success[(int) ch];
			}

			index = currentState->remove(keyword.size());
			assert_lt(index, 0);

			int numOfDeletion = parent.size();
			int character = currentState->deleteEmit(parent);

			if (character != -1) {
				numOfDeletion -= parent.size();
				deleteFailureStates((_CharT) character, keyword, numOfDeletion);
			}
			emit.pop_back();
		}
	}

//delete first, and then change second to first, 
	void removeIndex(int index) {
		int last = emit.size() - 1;
		std::swap(emit[index], emit[last]);

		root->removeIndex(index);
		Node *first_node, *second_node;
		first_node = second_node = nullptr;

		index = -index - 1;
		for (auto &node : this->node) {
			if (node.base == index) {
				first_node = &node;
				break;
			}
		}

		last = -last - 1;
		for (auto &node : this->node) {
			if (node.base == last) {
				second_node = &node;
				break;
			}
		}

		first_node->base = last;
		second_node->base = index;
	}

	void deleteFailureStates(_CharT character, const String &keyword,
			int numOfDeletion) {
		int char_length = keyword.size();

		vector<State*> list;
		int mid = keyword.size() - numOfDeletion;
		if (mid == 0) {
			list = root->locate_state(character);
			deleteFailureStates(list, keyword, char_length);
		} else {
			if (keyword.empty() || (int) keyword.size() < mid)
				return;

			list = root->locate_state(keyword.substr(0, mid));

			deleteFailureStates(list, keyword.substr(mid - 1), char_length);
		}
	}

	void deleteFailureStates(vector<State*> &list, const String &keyword,
			int char_length) {
		_CharT character = keyword[0];
		for (auto parent : list) {
			auto state = parent->success[(int) character];
			state->deleteFailureStates(parent, keyword, char_length);
		}
	}

	void put(const String &keyword, const V &value) {
		if (order < 0) {
		} else {
			int index = exactMatchSearch(keyword);
			if (index >= 0) {
				this->emit[index].value = value;
				return;
			}

			index = emit.size();
			emit.resize(emit.size() + 1);
			emit[index] = Emit { (int) keyword.size(), value };

			State *currentState = this->root;
			State *crutialState = nullptr;
			int crutialIndex = -1;
			State *parent = nullptr;
			vector<Transition> queue;
			for (size_t i = 0; i < keyword.size(); ++i) {
				_CharT ch = keyword[i];
				if (crutialState == nullptr)
					parent = currentState;
				currentState = currentState->addState(ch, queue);
				if (currentState->index == 0 && crutialState == nullptr) {
					crutialState = parent;
					crutialIndex = i;
				}
			}

			currentState->addEmit();
			if (crutialIndex >= 0) {
				_CharT ch = keyword[crutialIndex];
				update(crutialState, ch, index);
			}

			currentState->addEmit(emit.size() - 1);
			updateFailureStates(queue, keyword);
		}
	}

	void updateFailureStates(vector<Transition> &queue, const String &keyword) {
		for (auto &transit : queue) {
			transit.set_failure();
		}

		vector<State*> list;
		Transition keywordHead = { 0, 0 };

		if (!queue.empty()) {
			keywordHead = queue[0];
			if (!keywordHead.parent->isRoot()) {
				keywordHead.parent = nullptr;
			}
		}

		State *rootState = this->root;

		if (keywordHead.parent != nullptr) {
			list = keywordHead.parent->locate_state(keywordHead.character);
			constructFailureStates(list, rootState, keyword);
		} else {
			String oldKeyword = keyword;
			String _keyword;
			if (queue.empty()) {
				int mid = keyword.size();
				_keyword = keyword.substr(mid - 1);
			} else {
				int mid = keyword.size() - (queue.size() - 1);
				_keyword = keyword.substr(mid - 1);
				oldKeyword = keyword.substr(0, mid);
			}

			list = rootState->locate_state(oldKeyword);

			for (size_t i = 0; i < oldKeyword.size() - 1; ++i) {
				rootState = rootState->success[(int) oldKeyword[i]];
			}
//			keyword = _keyword;
			constructFailureStates(list, rootState, _keyword);
		}

	}

	void constructFailureStates(vector<State*> &list, State *rootState,
			const String &keyword) {
		_CharT character = keyword[0];
		for (auto parent : list) {
			auto state = parent->success[(int) character];
			state->constructFailureStates(parent, rootState, keyword);
		}
	}

	void update(State *parent, int word, int emit) {
		for (;;) {
			int code = parent->index;
			auto state = parent->success[word];
			int begin = node[code].base;
			int pos = 0;
			bool need_update_base;
			if (begin == 0) {
				need_update_base = true;
			} else {
				assert_or(code == 0, node[code].check != 0);
				pos = begin + (_CharT) (word + 1);
				need_update_base = node[pos].check != 0;
			}

			if (need_update_base) {
				begin = parent->update_base();
				pos = begin + (_CharT) (word + 1);
			}

			if (!used.isRegistered(begin)) {
				occupy(begin);
			}

			state->index = pos;

			assert_eq(node[pos].base, 0);
			node[pos].check = begin;

			if (node[code].base != begin) {
				recycle(node[code].base);

				for (auto &entry : parent->success) {
					int key = entry.first;
					if (key != word) {
						auto sibling = entry.second;
						node[sibling->index].clear();

						int new_code = begin + (_CharT) (key + 1);
						sibling->index = new_code;
						assert_eq(node[new_code].check, 0);
						node[new_code].check = begin;

						sibling->update_base();
					}
				}
				node[code].base = begin;
				assert_neq(node[code].check, 0);
			}

			if (state->is_null_terminator()) {
				state->emit(emit);
				break;
			}

			assert_eq(state->success.size(), 1);
			auto entry = state->success.begin();
			parent = state;
			word = entry->first;
		}
	}

	std::map<int, int> toTreeMap(const vector<int> &emit) const {
		std::map<int, int> map;

		for (int index : emit) {
			map[this->emit[index].char_length] = index;
		}

		return map;
	}

	static vector<int> toArray(const std::map<int, int> &map) {
		if (map.empty())
			return {};

		vector<int> emit(map.size());
		int i = 0;
		for (auto &entry : map) {
			int index = entry.second;
			emit[i++] = index;
		}
		return emit;
	}

	bool operator ==(const AhoCorasickDoubleArrayTrie &obj) const {
		if (to_map() != obj.to_map())
			return false;
		return *root == *obj.root;
	}

	std::map<int, std::set<V>> to_map() const {
		std::map<int, std::set<V>> map;
		for (auto &e : emit) {
			map[e.char_length].insert(e.value);
		}

		return map;
	}

	static State* newFailureState(State *currentState, int transition) {
		State *state;
		do {
			currentState = currentState->failure;
			state = currentState->nextState(transition);
		} while (state == nullptr);

		return state;
	}

	const static bool debug = true;
};

template<typename _CharT, typename V>
typename AhoCorasickDoubleArrayTrie<_CharT, V>::State* AhoCorasickDoubleArrayTrie<
		_CharT, V>::Transition::node() {
	return parent->success[character];
}

template<typename _CharT, typename V>
void AhoCorasickDoubleArrayTrie<_CharT, V>::Transition::set_failure() {
	if (parent->isRoot()) {
		parent->success[character]->setFailure(parent);
	} else {
		auto targetState = parent->success[character];
		auto newFailureState =
				AhoCorasickDoubleArrayTrie<_CharT, V>::newFailureState(parent,
						character);
		targetState->setFailure(newFailureState);

		targetState->addEmit(newFailureState->emit());
	}
}

void testLoop();

