#pragma once

struct Intervalable {
    int getStart();
    int getEnd();
    int size();
    bool equals(const Intervalable &) const ;
};
