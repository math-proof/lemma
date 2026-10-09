#pragma once
#include "utility.h"

template<typename Char = char16_t>
struct TextTreeNode {
	vector<TextTreeNode*> x, y;

	~TextTreeNode() {
		for (auto p : x) {
			delete p;
		}
		for (auto p : y) {
			delete p;
		}
	}
	// objects hold a formatted label string and the level,column
	// coordinates for a shadow tree node
	std::basic_string<Char> value; // formatted node value
	int i, j;

	TextTreeNode(const std::basic_string<Char> &value =
			std::basic_string<Char>()) :
			value(value) {
	}

	static int max_width(vector<TextTreeNode*> &list) {
		int length = 0;
		for (TextTreeNode *x : list) {
			int width = x->max_width();
			if (width > length) {
				length = width;
			}
		}
		return length;
	}

	int max_width() {
		int width = strlen(value);
		if (x.size()) {
			int width_x = max_width(x);
			if (width_x > width)
				width = width_x;
		}
		if (y.size()) {
			int width_y = max_width(y);
			if (width_y > width)
				width = width_y;
		}
		return width;
	}

	void hierarchize() {
		int column = 0;
		hierarchize(0, column);
	}

	static void hierarchize(vector<TextTreeNode*> &list, int level,
			int &column) {
		for (auto x : list) {
			x->hierarchize(level, column);
		}
	}

	void hierarchize(int level, int &column) {
		if (x.size())
			hierarchize(x, level + 1, column);
		// allocate node for left child at next level in tree; attach node
		i = level;
		j = column++; // update column to next cell in the table

		if (y.size())
			hierarchize(y, level + 1, column);
	}

	// the font type should be simsun;
	std::basic_string<Char> toString() {
		return std::toString(max_width());
	}

	void shrink(vector<TextTreeNode*> &x) {
		if (x.size() <= 1)
			return;
		TextTreeNode *curr, *prev;

		prev = x[0];
		for (size_t i = 1; i < x.size(); i++) {
			curr = x[i];
			int offset = shift(prev, curr);
			if (offset > 0)
				x[i]->offset(-offset);

			prev = x[i];
		}
	}

	void shrink(TextTreeNode *parent) {
		if (x.size())
			for (auto node : this->x) {
				node->shrink(this);
			}
		if (y.size())
			for (auto node : this->y) {
				node->shrink(this);
			}

		if (x.size()) {
			shrink(x);
			if (y.size()) {

				auto prev = x.back();
				auto curr = y[0];
				int offset = std::min(this->j - prev->j - 1, shift(prev, curr));

				if (offset > 0) {
					curr->offset(-offset);
					this->j -= offset;
					//				if (debug)
					//					this.value = String.valueOf(this->j);
				}

				shrink(y);

			}
		} else {
			if (y.size()) {
				shrink(y);
				int diff = y[0]->j - this->j;
				if (diff > 1) {
					auto left_most = y[0]->left_most();
					int left_most_j = left_most->j;
					if (left_most_j > this->j) {
						diff = this->j - left_most_j;
						offset(y, diff);
						if (parent != nullptr) {
							if (parent->hasLeftKinder(this)) {
								parent->j += diff;
								//							if (debug)
								//								parent->value = toString(parent->j);
							}
							offset(parent->rightSiblings(this), diff);
						}
					}
				}
			}
		}
	}

	std::basic_string<Char> toString(int max_width, bool shrink) {
		const static auto lineSeparator = u'\n';

		std::basic_string<Char> cout;
		int currLevel = 0;
		int currCol = 0;

		// build the shadow tree
		hierarchize();
		if (shrink)
			this->shrink(nullptr);

		// const int colWidth = Math.max(max_width, max_width()) + 1;
		const int colWidth = max_width;

		// use during the level order scan of the shadow tree
		TextTreeNode *currNode;
		//
		// store siblings of each nodeShadow object in a queue so that they
		// are visited in order at the next level of the tree
		std::queue<TextTreeNode*> q;
		//
		// insert the root in the queue and set current level to 0
		q.push(this);
		//
		// continue the iterative process until the queue
		// is empty
		while (q.size() != 0) {
			// delete front node from queue and make it the
			// current node
			currNode = q.front();
			q.pop();

			if (currNode->i > currLevel) {
				// if level changes, output a newline
				currLevel = currNode->i;
				currCol = 0;
				cout += lineSeparator;
			}

			char16_t ch;
			if (currNode->x.size()) {
				//				assert(currNode->x.length > 0);
				for (TextTreeNode *t : currNode->x)
					q.push(t);

				TextTreeNode *head = currNode->x[0];
				// the string is right-aligned / right-justified, that's why
				// there a series of leading ' ';
				int dif = colWidth - strlen(head->value);	// for leading ' 's
				cout += std::basic_string<Char>(
						(head->j - currCol) * colWidth + dif, u' ');
				cout += std::basic_string<Char>(
						(currNode->j - head->j) * colWidth - dif, u'_');

				ch = u'_';
			} else {
				cout += std::basic_string<Char>(
						(currNode->j - currCol) * colWidth, u' ');

				ch = u' ';
			}

			// for leading white spaces;
			cout += std::basic_string<Char>(colWidth - strlen(currNode->value),
					ch) + currNode->value;

			currCol = currNode->j;
			if (currNode->y.size()) {
				for (TextTreeNode *t : currNode->y)
					q.push(t);

				TextTreeNode *last = currNode->y[currNode->y.size() - 1];
				cout += std::basic_string<Char>((last->j - currCol) * colWidth,
						u'_');

				currCol = last->j;
			}

			++currCol;
		}
		cout += lineSeparator;

		return cout;
	}

	vector<TextTreeNode*> rightSiblings(TextTreeNode *kinder) {
		if (x.size()) {
			int index = indexOf(x, kinder);
			if (index >= 0) {
				if (y.size())
					return copier(copyOfRange(x, index + 1, x.size()), y);
				return copyOfRange(x, index + 1, x.size());
			}
		}

		int index = indexOf(y, kinder);
		assert_ge(index, 0);
		return copyOfRange(y, index + 1, y.size());

	}

	bool hasLeftKinder(TextTreeNode *kinder) {
		return x.size() && indexOf(x, kinder) >= 0;
	}

	static int shift(TextTreeNode *prev, TextTreeNode *curr) {
		int offset = curr->left_hand()->j - prev->right_hand()->j;

		do {
			prev = prev->last_kinder();
			curr = curr->first_kinder();
			if (prev == nullptr || curr == nullptr)
				break;
			offset = std::min(offset,
					curr->left_hand()->j - prev->right_hand()->j);
		} while (true);
		--offset;
		return offset;
	}

	TextTreeNode* right_hand() {
		if (y.size())
			return y.back();
		return this;
	}

	TextTreeNode* first_kinder() {
		if (x.size())
			return x[0];
		if (y.size())
			return y[0];
		return nullptr;
	}

	TextTreeNode* left_hand() {
		if (x.size())
			return x[0];
		return this;
	}

	TextTreeNode* last_kinder() {
		if (y.size())
			return y.back();
		if (x.size())
			return x.back();
		return nullptr;
	}

	static void offset(const vector<TextTreeNode*> &x, int dj) {
		for (auto node : x) {
			node->offset(dj);
		}
	}

	void offset(int dj) {
		this->j += dj;
		//	if (debug)
		//		this.value = String.valueOf(j);
		if (x.size())
			offset(x, dj);
		if (y.size())
			offset(y, dj);
	}

	TextTreeNode* left_most() {
		if (x.size())
			return x[0]->left_most();
		return this;
	}
};
