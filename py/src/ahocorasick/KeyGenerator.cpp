#include "KeyGenerator.h"
#include <assert.h>
#include <set>
#include <vector>
using std::vector;
#include <string>
using std::string;

bool KeyGenerator::Couplet::operator <(const Couplet &o) const {
	return x < o.x;
}

int KeyGenerator::elementSize() {
	int sum = 0;
	for (const Couplet &e : set) {
		sum += e.y - e.x;
	}
	return sum;
}

KeyGenerator& KeyGenerator::conjugate() {
	assert(!set.empty());

	auto curr = set.begin();

	auto prev = curr;
	for (++curr; curr != set.end(); ++curr) {
		(int&) prev->x = prev->y;
		(int&) prev->y = curr->x;
		prev = curr;
	}
	set.erase(prev);
	return *this;
}

vector<int> KeyGenerator::keySet() {
	vector<int> arr(elementSize());
	int i = 0;
	for (Couplet s : set) {
		for (int j = s.x; j < s.y; ++j) {
			arr[i++] = j;
		}
	}
	return arr;
}

string KeyGenerator::toString() const {
	string str = "";
	for (auto &s : set) {
		str += std::to_string(s.x) + " -> " + std::to_string(s.y) + " = "
				+ std::to_string(s.y - s.x);
		str += "\n";
	}
	return str;
}

void KeyGenerator::register_key(int key) {
	Couplet newElement = { key, key + 1 };

//	returns an iterator to the first element that is not less than val.
	auto mid_iter = set.lower_bound(newElement);

	if (mid_iter != set.end()) {
		assert(mid_iter->x > key);

		if (mid_iter != set.begin()) {
			auto prev = mid_iter;
			--prev;
			if (prev->y == key) {
				++(int&) prev->y;
				if (mid_iter->x == prev->y) {
					int prev_x = prev->x;
					auto curr = set.erase(prev);
					(int&) curr->x = prev_x;
				}
				return;
			} else if (mid_iter->x == key + 1) {
				--(int&) mid_iter->x;
				return;
			}

		}

	} else {
		auto rbegin = set.rbegin();
		if (rbegin != set.rend()) {
			Couplet &last = (Couplet&) *rbegin;
//			cout << "set.size = " << set.size() << endl;
			if (last.y == key) {
				++last.y;
//				cout << "set.size = " << set.size() << endl;
				return;
			}
		}
	}

	set.insert(newElement);
}

void KeyGenerator::sanity_check() {
	if (set.empty())
		return;
	auto prev = set.begin();
	auto curr = prev;
	for (++curr; curr != set.end(); ++curr) {
		assert(prev->y < curr->x);
		prev = curr;
	}
}

bool KeyGenerator::isRegistered(int key) {
	auto floor = set.upper_bound( { key, key + 1 });

	if (floor == set.begin()) {
		return false;
	}
	--floor;

	return key < floor->y;
}

void KeyGenerator::unregister_key(int key) {
	Couplet newElement = { key, key + 1 };
	//	returns an iterator to the first element that is not less than val.
	auto mid_iter = set.upper_bound(newElement);
	--mid_iter;
	assert(mid_iter->x <= key);

	if (mid_iter->x == key) {
		++(int&) mid_iter->x;
		if (mid_iter->x == mid_iter->y) {
			set.erase(mid_iter);
		}
	} else if (mid_iter->y == key + 1) {
		--(int&) mid_iter->y;
	} else {
		newElement = { key + 1, mid_iter->y };

		(int&) mid_iter->y = key;
		set.insert(newElement);
	}
}

int KeyGenerator::generate_key() {
	int key;
	if (set.size() == 0)
		key = initial_key;
	else
		key = set.begin()->y;
	register_key(key);
	return key;
}

int KeyGenerator::lower(int key) {
	Couplet element = { key, key + 1 };
	auto lower = set.lower_bound(element);
	if (lower != set.end()) {
		if (lower->y - 1 < key)
			return lower->y - 1;

		key = lower->y - 1;
		lower = set.lower_bound(*lower);
		if (lower != set.end()) {
			return lower->y - 1;
		}
	}

	return key;
}

KeyGenerator::iterator& KeyGenerator::iterator::operator++() {
	++key;
	if (curr != self->set.end() && this->key == curr->x) {
		key = curr->y;
		prev = curr;
		++curr;
	}

	return *this;
}

bool KeyGenerator::iterator::operator!=(iterator &other) {
	return key != other.key;
}

int KeyGenerator::iterator::operator*() {
	return key;
}

KeyGenerator::iterator KeyGenerator::TailSet::begin() {
	auto iter = self->set.upper_bound( { start, start + 1 });
	if (iter == self->set.begin()) {
		if (self->set.empty()) {
			return {self, self->set.end(), self->set.end(), start};
		}
		return {self, self->set.begin(), self->set.begin(), start};
	}
	auto prev = iter;
	--prev;
	if (start >= prev->y)
		return {self, prev, iter, start};
	return {self, prev, iter, prev->y};
}

KeyGenerator::iterator KeyGenerator::TailSet::end() {
	return {self, self->set.end(), self->set.end(), -1};
}

KeyGenerator::TailSet KeyGenerator::tailSet(int start) {
	return TailSet { this, start + 1 };
}

KeyGenerator::iterator KeyGenerator::begin() {

	auto prev = this->set.begin();
	if (prev == this->set.end()) {
		return {this, this->set.end(), this->set.end(), -1};
	}

	auto curr = prev;
	int start = prev->y;
	++curr;

	return {this, prev, curr, start};
}

KeyGenerator::iterator KeyGenerator::end() {
	return {this, this->set.end(), this->set.end(), -1};
}

#include <unordered_set>
void KeyGenerator::test() {
	seed_rand();

	KeyGenerator keyGenerator;

	const int size = 400;
	int arr[size];
	std::unordered_set<int> set;
	for (int i = 0; i < size; ++i) {
		int a;
		while (true) {
//				a = 1 + r.nextInt(4000);
			a = 100 + i * nextInt(4);

			if (set.count(a))
				continue;
			break;
		}
		arr[i] = a;
		set.insert(a);
	}

	cout << set << endl;

	for (int a : arr) {
		cout << "registering " << a << endl;
		keyGenerator.register_key(a);
		keyGenerator.sanity_check();
		cout << keyGenerator.toString() << endl;

		assert(keyGenerator.isRegistered(a));
	}

	keyGenerator.register_key(0);
	keyGenerator.register_key(1);

	vector<int> newKeys;
	for (int key : keyGenerator) {
		if (key == 99) {
			cout << "new key = " << key << endl;
		}
		newKeys.push_back(key);
		assert(!keyGenerator.isRegistered(key));
		if (newKeys.size() >= 2000)
			break;
	}

	assert(newKeys.size() >= 2000);
	cout << newKeys << endl;

	for (int fromElement = 0; fromElement < 2000; ++fromElement) {
		cout << "fromElement = " << fromElement << endl;

		int cnt = 0;
		int max_cnt = 10;
		for (int next : keyGenerator.tailSet(fromElement)) {
			cout << "next = " << next << endl;
			assert(next > fromElement);
			assert(!keyGenerator.isRegistered(next));
//			for (int j = fromElement + 1; j < next; ++j)
//				assert (keyGenerator.isRegistered(j));
			if (++cnt >= max_cnt)
				break;
		}
	}

	for (int a : set) {
		cout << keyGenerator.toString() << endl;
		assert(keyGenerator.isRegistered(a));
		keyGenerator.unregister_key(a);
		keyGenerator.sanity_check();

		assert(!keyGenerator.isRegistered(a));
	}

	cout << "test successfully!" << endl;
}
