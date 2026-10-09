#pragma once
#include "../std/utility.h"
#include "AhoCorasickDoubleArrayTrie.h"

template<typename Value>
struct Knapsack {
	using Hit = typename AhoCorasickDoubleArrayTrie<char16_t, Value>::Hit;
	vector<bool> occupied;
	vector<Hit> &partsGiven;
	vector<Hit*> partsUsed;
	vector<Hit*> partsUnused;
	vector<Hit*> partsSpare;
	float (*score) (Hit*);

	Knapsack(int strlen, const vector<Hit> &partsGiven, float (*score) (Hit*)) :
			occupied(strlen),
			partsGiven((vector<Hit>&) partsGiven),
			score(score){
		partsSpare.reserve(2);
	}

	void add(Hit *part) {
		partsUsed.push_back(part);
		occupy(part);
	}

	void add(Hit &part) {
		add(&part);
	}

	void add(int index, Hit *part) {
		partsUsed.insert(partsUsed.begin() + index, part);
		occupy(part);
	}

	void update(int index, Hit *part) {
		auto prev = partsUsed[index];
		deoccupy(prev);

		partsUsed[index] = part;

		occupy(part);

		partsUnused.push_back(prev);
	}

    void update(vector<int> &slice, Hit *part) {
        int start = slice[0];
        int stop = slice[1];
        for (int i = start; i < stop; ++i) {
        	auto prev = partsUsed[start];
            partsUsed.erase(partsUsed.begin() + start);
            deoccupy(prev);
            partsUnused.push_back(prev);
        }

        partsUsed.insert(partsUsed.begin() + start, part);
        occupy(part);
    }

	Hit* remove(int index) {
		auto part = partsUsed[index];
		deoccupy(part);
		partsUsed.erase(partsUsed.begin() + index);
		partsUnused.push_back(part);
		return part;
	}

	bool is_occupied(const Hit &givenPart) {
		for (int i = givenPart.begin; i < givenPart.end; ++i) {
			if (occupied[i])
				return true;
		}
		return false;
	}

	void occupy(const Hit *part) {
		for (int i = part->begin; i < part->end; ++i) {
			occupied[i] = true;
		}
	}

	void deoccupy(const Hit *part) {
		for (int i = part->begin; i < part->end; ++i) {
			occupied[i] = false;
		}
	}

	int numOfBlocksCovered(const Hit *part, int skip=0) {
		int sum = 0;
		for (int i = partsUsed.size() - 1 - skip; i >= 0; --i) {
			if (!partsUsed[i]->intersects(part))
				break;
			++sum;
		}
		return sum;
	}

    vector<int> sliceOfBlocksCovered(const Hit *part) {
        int stop = partsUsed.size();
        for (; stop > 0; --stop) {
            if (partsUsed[stop - 1]->intersects(part)) {
                break;
            }
        }

        if (stop == 0)
            return {};

        int start = stop - 1;
        for (; start > 0; --start) {
            if (!partsUsed[start - 1]->intersects(part)) {
                break;
            }
        }
        return {start, stop};
    }

	float scoreOfBlocksCovered(int sum) {
		double score = 0;
		for (int i = partsUsed.size() - 1, j = 0; j < sum; --i, ++j) {
			score += this->score(partsUsed[i]);
		}
		return score;
	}

    float scoreOfBlocksCovered(const vector<int> &slice) {
        int start = slice[0];
        int stop = slice[1];
        float score = 0;
        for (int i = start; i < stop; ++i) {
            score += this->score(partsUsed[i]);
        }
        return score;
    }

	vector<Hit*> &cut() {
		for (auto &givenPart : partsGiven) {
			if (is_occupied(givenPart)) {
				partsSpare.push_back(&givenPart);
				continue;
			}

			if (partsSpare.empty()) {
				add(givenPart);
				continue;
			}

			Hit *sparePart = partsSpare.back();

			if (sparePart->end < partsUsed.back()->end) {
				partsSpare.clear();
				add(givenPart);
				continue;
			}

			intersects(givenPart);
		}

		if (!partsSpare.empty()) {
			auto sparePart = partsSpare.back();
			auto usedPart = partsUsed.back();
			auto numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
			if (numOfBlocksCovered >= 1){
				if (sparePart->end >= usedPart->end) {
					intersects(numOfBlocksCovered);
				}
			}
		}
		return partsUsed;
	}

	void update_consecutive(int num, Hit *part) {
		vector<Hit*> list;
		int stop = partsUnused.size();

		for (int cnt = 0; cnt < num; ++cnt) {
			list.push_back(remove(partsUsed.size() - 1));
		}

		add(part);

		if (stop > 0) {
			for (int k = 0; k < stop; ++k) {
				auto partAbandoned = partsUnused[k];
				int index = binary_search(partAbandoned);
				//is the boundary check necessary?
				if (index < partsUsed.size() && !partsUsed[index]->intersects(partAbandoned)) {
					add(index, partAbandoned);
					partsUnused.erase(partsUnused.begin() + k);
					--stop;
				}
			}
		}
	}

	void update_consecutive(int numOfBlocksCovered, Hit *sparePart, float score){
		auto begin = partsUsed[partsUsed.size() - numOfBlocksCovered]->begin;
		auto end = sparePart->begin;
		Hit *hit = nullptr;

        while (!partsUnused.empty()) {
            auto _hit = pop_back(partsUnused);
            if (_hit->begin >= begin && _hit->end <= end) {
                if (!hit || this->score(_hit) > this->score(hit)) {
                    hit = _hit;
                }
            }
            else {
                break;
            }
        }

        if (hit) {
            if (this->score(hit) + this->score(sparePart) > score) {
                update_consecutive(numOfBlocksCovered, hit);
                add(sparePart);
            }
        }
	}

	void intersects(Hit &givenPart) {
		intersects(&givenPart);
	}

	void intersects(Hit *givenPart) {
		auto sparePart = this->sparePart();
		int numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
		if (!numOfBlocksCovered) {
			auto slice = sliceOfBlocksCovered(sparePart);
			if (slice.empty()) {
				if (score(sparePart) > score(givenPart)) {
					update(partsUsed.size() - 1, sparePart);
				}
			}
			else {
                if (score(sparePart) > scoreOfBlocksCovered(slice)) {
                    update(slice, sparePart);
                    partsSpare.pop_back();
                    if (partsSpare.size())
                        intersects(givenPart);
                    return;
                }
			}

			partsSpare.clear();
		}
		else if (sparePart->intersects(givenPart)) {
			if (numOfBlocksCovered > 1) {
				if (score(sparePart) > score(givenPart) + scoreOfBlocksCovered(numOfBlocksCovered)) {
					update_consecutive(numOfBlocksCovered, sparePart);
					partsSpare.clear();
				} else {
					add(givenPart);
				}
			} else {
				auto usedPart = this->usedPart();
				auto diff = score(sparePart) - score(givenPart);
				if (diff > score(usedPart)) {
					auto secondLastSparePart = this->secondLastSparePart();
					if (secondLastSparePart == nullptr ||
                			!secondLastSparePart->intersects(sparePart) ||
                			diff >= score(secondLastSparePart)) {
						update(partsUsed.size() - 1, sparePart);
						partsSpare.pop_back();
						return;
					}
				}

				if (partsSpare.size() >= 3) {
					partsSpare.pop_back();
					intersects(givenPart);
					return;
				}

				if (partsSpare.size() == 2) {
					sparePart = partsSpare[0];
					numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
					if (!sparePart->intersects(givenPart)) {
						if (score(sparePart) > score(usedPart)) {
							partsSpare.pop_back();
							non_intersects(givenPart, numOfBlocksCovered);
							return;
						}
					}
				}

				add(givenPart);
			}
		} else
			non_intersects(givenPart, numOfBlocksCovered);
	}

	void intersects(int numOfBlocksCovered) {
		auto sparePart = pop_back(partsSpare);
		if (numOfBlocksCovered > 1) {
			auto score = scoreOfBlocksCovered(numOfBlocksCovered);
			if (this->score(sparePart) > score) {
				update_consecutive(numOfBlocksCovered, sparePart);
			}
			else{
				update_consecutive(numOfBlocksCovered, sparePart, score);
			}

			if (partsSpare.empty())
				return;

			sparePart = this->sparePart();
			auto usedPart = this->usedPart();

			numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
			if (sparePart->end >= usedPart->end && sparePart->intersects(usedPart))
				intersects(numOfBlocksCovered);

		} else {
			auto usedPart = this->usedPart();
			if (score(sparePart) > score(usedPart)) {
				update(partsUsed.size() - 1, sparePart);
				usedPart = this->usedPart();
			}

			int index = partsUsed.size() - 1;
			int skip = 1;
			while (!partsSpare.empty()) {
				sparePart = pop_back(partsSpare);
				if (sparePart->intersects(usedPart)) {
					if (this->numOfBlocksCovered(sparePart) == 1 && score(sparePart) > score(usedPart)) {
						update(partsUsed.size() - 1, sparePart);
						usedPart = this->usedPart();
					}
					continue;
				}

				if (index <= 0)
					break;

				usedPart = partsUsed[--index];
				if (sparePart->end >= usedPart->end
						&& sparePart->intersects(usedPart)
						&& this->numOfBlocksCovered(sparePart, skip) == 1
						&& score(sparePart) > score(usedPart)) {
					update(partsUsed.size() - 1 - skip, sparePart);
					++skip;
				}
			}

			partsSpare.clear();
		}
	}

	void non_intersects(Hit *givenPart, int numOfBlocksCovered) {
		Hit *sparePart = this->sparePart();
		if (numOfBlocksCovered > 1) {
			auto score = scoreOfBlocksCovered(numOfBlocksCovered);

			if (this->score(sparePart) > score)
				update_consecutive(numOfBlocksCovered, sparePart);
			else
				update_consecutive(numOfBlocksCovered, sparePart, score);

			partsSpare.pop_back();
			if (!partsSpare.empty()) {
				auto old_sparePart = sparePart;
				sparePart = partsSpare.back();
				numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
				if (sparePart->intersects(old_sparePart)) {
					non_intersects(givenPart, numOfBlocksCovered);
					return;
				}

				partsSpare.clear();
			}
		} else if (numOfBlocksCovered) {
			auto usedPart = this->usedPart();
			if (score(sparePart) > score(usedPart))
				update(partsUsed.size() - 1, sparePart);
			else
				partsUnused.push_back(sparePart);
			partsSpare.pop_back();

			if (!partsSpare.empty()) {
				auto old_sparePart = sparePart;
				sparePart = partsSpare.back();
				numOfBlocksCovered = this->numOfBlocksCovered(sparePart);
				if (sparePart->intersects(old_sparePart)) {
					non_intersects(givenPart, numOfBlocksCovered);
					return;
				}

				bool needUpdate;
				if (sparePart->intersects(usedPart)) {
					needUpdate = sparePart->end >= usedPart->end
							&& sparePart->begin != usedPart->begin
							&& !sparePart->intersects(givenPart)
							&& numOfBlocksCovered == 1
							&& score(sparePart) > score(usedPart);
					// is the following line necessary?
					needUpdate = needUpdate && partsUsed.size() >= 2;
				} else {
					if (partsUsed.size() >= 2){
						auto secondLast = partsUsed[partsUsed.size() - 2];
						needUpdate = secondLast->begin == sparePart->begin && sparePart->end > secondLast->end;
					}
					else{
						needUpdate = false;
					}
				}

				if (needUpdate)
					update(partsUsed.size() - 2, sparePart);

				partsSpare.clear();
			}
		}

		add(givenPart);
	}

	int binary_search(Hit *part) {
		return ::binary_search(partsUsed, part, &Knapsack::compare_hit);
	}

	static int compare_hit(Hit *o1, Hit *o2) {
		if (o1->end <= o2->begin)
			return -1;

		if (o1->begin >= o2->end)
			return 1;

		return 0;
	}

	Hit *usedPart(){
		return partsUsed.back();
	}

	Hit *sparePart(){
		return partsSpare.back();
	}

	Hit *secondLastSparePart(){
		auto size = partsSpare.size();
		if (size > 1)
			return partsSpare[size - 2];
		return nullptr;
	}
};
