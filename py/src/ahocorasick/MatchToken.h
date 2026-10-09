#include "Token.h"
#include "Emit.h"

struct MatchToken: Token {

	Emit emit;

	MatchToken(String fragment, Emit emit) :
			Token(fragment), emit(emit) {
	}

	bool isMatch() {
		return true;
	}

	Emit getEmit() {
		return this->emit;
	}

};
