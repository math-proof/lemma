#include "Token.h"

struct FragmentToken: Token {

	FragmentToken(String fragment) :
			Token(fragment) {
	}

	bool isMatch() {
		return false;
	}

//	Emit getEmit() {
//		return Emit();
//	}
};
