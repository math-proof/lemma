#include "Intervalable.h"

class IntervalableComparatorBySize {


    int compare(Intervalable intervalable, Intervalable intervalable2) {
        int comparison = intervalable2.size() - intervalable.size();
        if (comparison == 0) {
            comparison = intervalable.getStart() - intervalable2.getStart();
        }
        return comparison;
    }

};
