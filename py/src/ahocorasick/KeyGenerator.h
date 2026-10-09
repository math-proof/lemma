#pragma once
#include "../std/utility.h"

struct KeyGenerator {
	/**
	 * 
	 */

	struct Couplet {
		int x, y;

		bool operator <(const Couplet &o) const;
	};

	std::set<Couplet> set;

	int elementSize();

	KeyGenerator& conjugate();

	vector<int> keySet();

	string toString() const;

	friend std::ostream& operator <<(std::ostream &cout, const KeyGenerator &p) {
		return cout << p.toString();
	}

	void register_key(int key);

	bool isRegistered(int key);

	void unregister_key(int key);

	void sanity_check();

	int generate_key();

	int lower(int key);

	static void test();

	struct iterator {
		KeyGenerator *self;
		std::set<Couplet>::iterator prev, curr;
		int key;

		iterator& operator++();
		bool operator!=(iterator &other);
		int operator*();
	};

	iterator begin();
	iterator end();

	struct TailSet {
		KeyGenerator *self;
		int start;


		iterator begin();
		iterator end();
	};

	TailSet tailSet(int start);

	const static int initial_key = 0;
};
