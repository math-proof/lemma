/**
 * <p>
 * A state has various important tasks it must attend to:
 * </p>
 *
 * <ul>
 * <li>success; when a character points to another state, it must return that
 * state</li>
 * <li>failure; when a character has no matching state, the algorithm must be
 * able to fall back on a state with less depth</li>
 * <li>emits; when this state is passed and keywords have been matched, the
 * matches must be 'emitted' so that they can be used later on.</li>
 * </ul>
 *
 * <p>
 * The root state is special in the sense that it has no failure state; it
 * cannot fail. If it 'fails' it will still parse the next character and start
 * from the root node. This ensures that the algorithm always runs. All other
 * states always have a fail state.
 * </p>
 *
 * @author Robert Bor
 */
#include "../std/utility.h"
#include <map>

#include "../std/TextTreeNode.h"
using std::map;
#include <queue>

struct State {

	/** effective the size of the keyword */
	const size_t depth;

	/**
	 * referred to in the white paper as the 'goto' structure. From a state it is
	 * possible to go to other states, depending on the character passed.
	 */
//	std::map<char16_t, State*> success;
	std::unordered_map<char16_t, State*> success;

	~State();

	/** if no matching states are found, the failure state will be returned */
	State *failure = nullptr;

	/**
	 * whenever this state is reached, it will emit the matches keywords for future
	 * reference
	 */

	struct Tuple {
		size_t char_length;
		String value;
	};

	bool operator ==(const State &obj) const;
	bool operator !=(const State &obj) const;
	vector<Tuple> emits;

	TextTreeNode<char16_t>* toShadowTree();
	String toString();

	State(int depth = 0);
	State* nextState(char16_t character);

	State* addState(char16_t character);

	void locate_state(char16_t ch, vector<State*> &list);

	void locate_state(const String &prefix, const String &keyword,
			vector<State*> &list);

	vector<State*> locate_state(char16_t ch);

	vector<State*> locate_state(const String &keyword);

	struct Transition {
		char16_t character;
		State *parent;

		Transition(char16_t character, State *state);

		State* node();

		void set_failure();
	};

	static void constructFailureStates(vector<State*> &list, State *rootState,
			const String &keyword);

	static void deleteFailureStates(vector<State*> &list, const String &keyword,
			int char_length);

	static State* newFailureState(State *currentState, char16_t transition);

	State* updateState(char16_t character, vector<Transition> &queue);

	void addEmit(const Tuple &tuple);

	void updateEmit(const Tuple &tuple);

	void deleteEmit(size_t char_length);

	void addEmit(vector<Tuple> &emits);

	void updateEmit(const vector<Tuple> &emits);

	bool update_failure(State *parent, char16_t ch);
	bool delete_failure(State *parent, char16_t ch);

	State* update_failure(State *parent, char16_t ch, State *keywordNode);
	void constructFailureStates(State *parent, State *rootState,
			const String &keyword);

	void constructFailureStates_(State *parent, State *rootState,
			const String &keyword);

	void deleteFailureStates(State *parent, const String &keyword,
			int char_length);
};

bool operator == (const std::unordered_map<char16_t, State*> &lhs, const std::unordered_map<char16_t, State*> &rhs);
//bool operator != (const std::map<char16_t, State*> &lhs, const std::map<char16_t, State*> &rhs);
