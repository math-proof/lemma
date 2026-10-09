#pragma once

#include "Interval.h"

struct Emit: Interval {
	const char16_t *value;

	Emit(int start, int end, const String &value);

	String toString();
};
