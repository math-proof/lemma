#include "../std/utility.h"
#include "Emit.h"

struct Token {
    String fragment;

    Token(String fragment) {
        this->fragment = fragment;
    }

    String getFragment() {
        return this->fragment;
    }

    bool isMatch();

    Emit getEmit();
};
