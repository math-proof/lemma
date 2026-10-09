#include "IntervalNode.h"

class IntervalTree {

    object<IntervalNode> rootNode = nullptr;

    IntervalTree(vector<Intervalable> &intervals) {
        this->rootNode = new IntervalNode(intervals);
    }

    vector<Intervalable> removeOverlaps(vector<Intervalable> &intervals) {

        // Sort the intervals on size, then left-most position
        Collections.sort(intervals, new IntervalableComparatorBySize());

        Set<Intervalable> removeIntervals = new TreeSet<Intervalable>();

        for (Intervalable interval : intervals) {
            // If the interval was already removed, ignore it
            if (removeIntervals.contains(interval)) {
                continue;
            }

            // Remove all overallping intervals
            removeIntervals.addAll(findOverlaps(interval));
        }

        // Remove all intervals that were overlapping
        for (Intervalable removeInterval : removeIntervals) {
            intervals.remove(removeInterval);
        }

        // Sort the intervals, now on left-most position only
        Collections.sort(intervals, new IntervalableComparatorByPosition());

        return intervals;
    }

    vector<Intervalable> findOverlaps(Intervalable interval) {
        return rootNode.findOverlaps(interval);
    }

};
