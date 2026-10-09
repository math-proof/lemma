/**
 *
 * Based on the Aho-Corasick white paper, Bell technologies:
 * ftp://163.13.200.222/assistant/bearhero/prog/%A8%E4%A5%A6/ac_bm.pdf
 * 
 * @author Robert Bor
 */
#include "Trie.h"

Trie::Trie(const std::map<String, String> &dictionaryMap,
		const TrieConfig &trieConfig) :
		dictionaryMap(dictionaryMap), trieConfig(trieConfig), rootState(
				new State()) {
	this->build();
}

Trie* Trie::caseInsensitive() {
	this->trieConfig.setCaseInsensitive(true);
	return this;
}

Trie* Trie::removeOverlaps() {
	this->trieConfig.setAllowOverlaps(false);
	return this;
}

Trie* Trie::onlyWholeWords() {
	this->trieConfig.setOnlyWholeWords(true);
	return this;
}

void Trie::addKeyword(const String &keyword, const String &value) {
	if (keyword.size() == 0) {
		return;
	}
	State *currentState = this->rootState;
	for (auto character : keyword) {
		currentState = currentState->addState(character);
	}

	currentState->addEmit(State::Tuple( { keyword.size(), value }));
}

void Trie::update(const String &keyword, const String &value) {
	if (keyword.empty()) {
		return;
	}

	vector<State::Transition> start;

	State *currentState = this->rootState;
	for (auto character : keyword) {
		currentState = currentState->updateState(character, start);
	}
	currentState->updateEmit(State::Tuple( { keyword.size(), value }));

	updateFailureStates(start, keyword);
}

void Trie::erase(const String &keyword) {
	if (keyword.size() == 0) {
		return;
	}

//		if (keyword.equals("意思"))
//			System.out.printf("delete %s\n", keyword);

	State *currentState = this->rootState;
	std::stack<State*> parent;
	for (auto character : keyword) {
		parent.push(currentState);
		try {
			currentState = currentState->success.at(character);
		} catch (std::out_of_range&) {
			return;
		}
	}

	currentState->deleteEmit(keyword.size());

	char16_t character = 0;
	int numOfDeletion = 0;
	for (size_t i = keyword.size() - 1; i != String::npos; --i) {
		if (!currentState->success.empty())
			break;

		bool tobebroken = false;
		for (auto &tuple : currentState->emits) {
			if (tuple.char_length == i + 1) {
				tobebroken = true;
				break;
			}
		}
		if (tobebroken) {
			break;
		}

		character = keyword[i];
		currentState = parent.top();
		parent.pop();

		currentState->success.erase(character);
		++numOfDeletion;
	}

	deleteFailureStates(currentState, character, keyword, numOfDeletion);
}

void Trie::build() {
	for (auto &p : dictionaryMap) {
		addKeyword(p.first, p.second);
	}
	constructFailureStates();
}

//	vector<Token> Trie::tokenize(String text) {
//
//		vector<Token> tokens;
//
//		vector<Emit> collectedEmits = parseText(text);
//		int lastCollectedPosition = -1;
//		for (Emit emit : collectedEmits) {
//			if (emit.getStart() - lastCollectedPosition > 1) {
//				tokens.push_back(createFragment(emit, text, lastCollectedPosition));
//			}
//			tokens.push_back(createMatch(emit, text));
//			lastCollectedPosition = emit.getEnd();
//		}
//		if (text.size() - lastCollectedPosition > 1) {
//			tokens.push_back(createFragment(nullptr, text, lastCollectedPosition));
//		}
//
//		return tokens;
//	}

//	Token Trie::createFragment(Emit emit, String text, int lastCollectedPosition) {
//		return new FragmentToken(
//				text.substr(lastCollectedPosition + 1,
//						emit == nullptr ? text.size() : emit.getStart()));
//	}
//
//	Token Trie::createMatch(Emit emit, String text) {
//		return new MatchToken(text.substr(emit.getStart(), emit.getEnd() + 1),
//				emit);
//	}

vector<Emit> Trie::parseText(const String &text) {

	int position = 0;
	State *currentState = this->rootState;
	vector<Emit> emits;
	emits.reserve(text.size());

	for (char16_t character : text) {
//			if (trieConfig.isCaseInsensitive()) {
//				character = Character.toLowerCase(character);
//			}
		currentState = getState(currentState, character);
		storeEmits(++position, currentState, emits);
	}

	if (trieConfig.isOnlyWholeWords()) {
//			removePartialMatches(text, collectedEmits);
	}

	if (!trieConfig.isAllowOverlaps()) {
//			IntervalTree intervalTree = IntervalTree(collectedEmits);
//			intervalTree.removeOverlaps(collectedEmits);
	}

	return emits;
}

vector<Emit> Trie::parseText(const unsigned short *text, int length) {
	vector<Emit> emits;
//	emits.reserve(length / 2);
	emits.reserve(length);
	int position = 0;
	State *currentState = this->rootState;
	for (int i = 0; i < length; ++i) {
		auto character = text[i];
//			if (trieConfig.isCaseInsensitive()) {
//				character = Character.toLowerCase(character);
//			}
		currentState = getState(currentState, character);
		storeEmits(++position, currentState, emits);
	}

	if (trieConfig.isOnlyWholeWords()) {
//			removePartialMatches(text, collectedEmits);
	}

	if (!trieConfig.isAllowOverlaps()) {
//			IntervalTree intervalTree = IntervalTree(collectedEmits);
//			intervalTree.removeOverlaps(collectedEmits);
	}
	return emits;
}

//	void Trie::removePartialMatches(String searchText, vector<Emit> collectedEmits) {
//		long size = searchText.size();
//		vector<Emit> removeEmits;
//		for (Emit emit : collectedEmits) {
//			if ((emit.getStart() == 0
//					|| !Character.isAlphabetic(
//							searchText.charAt(emit.getStart() - 1)))
//					&& (emit.getEnd() + 1 == size
//							|| !Character.isAlphabetic(
//									searchText.charAt(emit.getEnd() + 1)))) {
//				continue;
//			}
//			removeEmits.add(emit);
//		}
//
//		for (Emit removeEmit : removeEmits) {
//			collectedEmits.remove(removeEmit);
//		}
//	}

State* Trie::getState(State *currentState, char16_t transition) {
	for (;;) {
		State *state = currentState->nextState(transition);
		if (state != nullptr)
			return state;
		currentState = currentState->failure;
	}
}

void Trie::constructFailureStates() {
	std::queue<State*> queue;

// First, set the fail state of all depth 1 states to the root state
	for (auto &p : rootState->success) {
		State *depthOneState = p.second;
		depthOneState->failure = rootState;
		queue.push(depthOneState);
	}

// Second, determine the fail state for all depth > 1 state
	while (!queue.empty()) {
		State *currentState = queue.front();
		queue.pop();

		for (auto &p : currentState->success) {
			State *targetState = p.second;
			queue.push(targetState);

			State *newFailureState = State::newFailureState(currentState,
					p.first);
			targetState->failure = newFailureState;
			targetState->addEmit(newFailureState->emits);
		}
	}
}

void Trie::updateFailureStates(vector<State::Transition> &queue,
		String keyword) {
	for (auto &transit : queue) {
		transit.set_failure();
	}

	State::Transition *keywordHead = nullptr;
	if (!queue.empty()) {
		State::Transition *keywordHead = &queue[0];
		if (keywordHead->parent->depth != 0) {
			keywordHead = nullptr;
		}
	}

	State *rootState = this->rootState;
	vector<State*> list;
	if (keywordHead) {
		list = keywordHead->parent->locate_state(keywordHead->character);
	} else {
		String _keyword;
		if (queue.empty()) {
			int mid = keyword.size();
			_keyword = keyword.substr(mid - 1);
		} else {
			int mid = keyword.size() - (queue.size() - 1);
			_keyword = keyword.substr(mid - 1);
			keyword = keyword.substr(0, mid);
		}

		list = rootState->locate_state(keyword);

		for (size_t i = 0; i < keyword.size() - 1; ++i) {
			rootState = rootState->success.at(keyword[i]);
		}
		keyword = _keyword;
	}

	State::constructFailureStates(list, rootState, keyword);
}

void Trie::deleteFailureStates(State *parent, char16_t character,
		String keyword, int numOfDeletion) {
	int char_length = keyword.size();
	State *rootState = this->rootState;
	vector<State*> list;
	if (parent->depth == 0) {
		list = parent->locate_state(character);
	} else {
		size_t mid = keyword.size() - numOfDeletion;
		String _keyword = keyword.substr(mid - 1);
		if (keyword.empty() || keyword.size() < mid)
			return;

		keyword = keyword.substr(0, mid);
		list = rootState->locate_state(keyword);

		keyword = _keyword;
	}

	State::deleteFailureStates(list, keyword, char_length);
}

void Trie::clear() {
	rootState = new State;
	dictionaryMap.clear();
}

void Trie::storeEmits(int position, State *currentState,
		vector<Emit> &collectedEmits) {
//	auto iter = collectedEmits.end();
	for (auto &emit : currentState->emits) {
		collectedEmits.push_back(
				Emit(position - emit.char_length, position, emit.value));
	}
}
