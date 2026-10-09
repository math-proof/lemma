#include "../std/utility.h"
#include "Emit.h"

Emit::Emit(int start, int end, const String &value) :
		Interval(start, end), value(value.data()) {
}

String Emit::toString() {
	return Interval::toString() + u"=" + this->value;
}


