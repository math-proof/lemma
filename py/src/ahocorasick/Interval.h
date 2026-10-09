#pragma once

#include "Intervalable.h"
struct Interval: Intervalable {

	int start;
	int end;
	Interval(int start, int end) {
		this->start = start;
		this->end = end;
	}

	int getStart() {
		return this->start;
	}

	int getEnd() {
		return this->end;
	}

	int size() {
		return end - start + 1;
	}

	bool overlapsWith(Interval other) {
		return this->start <= other.getEnd() && this->end >= other.getStart();
	}

	bool overlapsWith(int point) {
		return this->start <= point && point <= this->end;
	}

	bool equals(Intervalable other) {
		return this->start == other.getStart() && this->end == other.getEnd();
	}

	int hashCode() {
		return this->start % 100 + this->end % 100;
	}

	int compareTo(Intervalable other) {
		int comparison = this->start - other.getStart();
		return comparison != 0 ? comparison : this->end - other.getEnd();
	}

	String toString() {
	    static std::basic_ostringstream<char16_t> stream;
	    stream.clear();

	    stream << this->start << ":" << this->end;

		return stream.str();
	}

};
