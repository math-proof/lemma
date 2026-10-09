class IntervalableComparatorByPosition {

public:
	int compare(Intervalable intervalable, Intervalable intervalable2) {
		return intervalable.getStart() - intervalable2.getStart();
	}

};
