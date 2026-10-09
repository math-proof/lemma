#include <iostream>
#include "hash/RabinKarp.h"
#include "std/utility.h"

using namespace std;
int main() {
    // [`0-9a-zA-Z=\[\]\\;',./~!@#$%^&*()_+{}|:'<>?" \n\t-]{8}
    // [\u2E80-\u2E99\u2E9B-\u2EF3\u2F00-\u2FD5\u3005\u3007\u3021-\u3029\u3038-\u303B\u3400-\u4DBF\u4E00-\u9FFF\uF900-\uFA6D\uFA70-\uFAD9：、！（），。、《》？：；“”【】]{8}
    // RabinKarp(TextC("hash/test/test-23.txt").read()).test();
    // return 0;
    for (int i: range(27)) {
        std::stringstream ss;
        ss << "hash/test/test-" << i << ".txt";
        RabinKarp(TextC(ss.str()).read()).test();
    }
    return 0;
}