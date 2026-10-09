#include "../../../eigenDebug/src/std/utility.h"
#include "Intervalable.h"

struct IntervalNode {
    enum Direction { LEFT, RIGHT };

    object<IntervalNode> left = nullptr;
    object<IntervalNode> right = nullptr;
    int point;
    vector<Intervalable> intervals;

    IntervalNode(vector<Intervalable> &intervals) {
        this->point = determineMedian(intervals);

        vector<Intervalable> toLeft;
        vector<Intervalable> toRight;

        for (Intervalable &interval : intervals) {
            if (interval.getEnd() < this->point) {
                toLeft.push_back(interval);
            } else if (interval.getStart() > this->point) {
                toRight.push_back(interval);
            } else {
                this->intervals.push_back(interval);
            }
        }

        if (toLeft.size() > 0) {
            this->left = new IntervalNode(toLeft);
        }
        if (toRight.size() > 0) {
            this->right = new IntervalNode(toRight);
        }
    }

    int determineMedian(vector<Intervalable> &intervals) {
        int start = -1;
        int end = -1;
        for (Intervalable &interval : intervals) {
            int currentStart = interval.getStart();
            int currentEnd = interval.getEnd();
            if (start == -1 || currentStart < start) {
                start = currentStart;
            }
            if (end == -1 || currentEnd > end) {
                end = currentEnd;
            }
        }
        return (start + end) / 2;
    }

    vector<Intervalable> findOverlaps(Intervalable &interval) {

        vector<Intervalable> overlaps;

        if (this->point < interval.getStart()) { // Tends to the right
            addToOverlaps(interval, overlaps, findOverlappingRanges(this->right, interval));
            addToOverlaps(interval, overlaps, checkForOverlapsToTheRight(interval));
        } else if (this->point > interval.getEnd()) { // Tends to the left
            addToOverlaps(interval, overlaps, findOverlappingRanges(this->left, interval));
            addToOverlaps(interval, overlaps, checkForOverlapsToTheLeft(interval));
        } else { // Somewhere in the middle
            addToOverlaps(interval, overlaps, this->intervals);
            addToOverlaps(interval, overlaps, findOverlappingRanges(this->left, interval));
            addToOverlaps(interval, overlaps, findOverlappingRanges(this->right, interval));
        }

        return overlaps;
    }

    void addToOverlaps(Intervalable &interval, vector<Intervalable> &overlaps, const vector<Intervalable> &newOverlaps) {
        for (auto &currentInterval : newOverlaps) {
            if (!currentInterval.equals(interval)) {
                overlaps.push_back(currentInterval);
            }
        }
    }

    vector<Intervalable> checkForOverlapsToTheLeft(Intervalable &interval) {
        return checkForOverlaps(interval, Direction::LEFT);
    }

    vector<Intervalable> checkForOverlapsToTheRight(Intervalable &interval) {
        return checkForOverlaps(interval, Direction::RIGHT);
    }

    vector<Intervalable> checkForOverlaps(Intervalable interval, Direction direction) {

        vector<Intervalable> overlaps;
        for (Intervalable &currentInterval : this->intervals) {
            switch (direction) {
                case LEFT :
                    if (currentInterval.getStart() <= interval.getEnd()) {
                        overlaps.push_back(currentInterval);
                    }
                    break;
                case RIGHT :
                    if (currentInterval.getEnd() >= interval.getStart()) {
                        overlaps.push_back(currentInterval);
                    }
                    break;
            }
        }
        return overlaps;
    }


    vector<Intervalable> findOverlappingRanges(IntervalNode *node, Intervalable &interval) {
        if (node != nullptr) {
            return node->findOverlaps(interval);
        }
        return vector<Intervalable>();
    }

};
