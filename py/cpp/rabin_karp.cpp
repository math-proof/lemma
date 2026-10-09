#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "../src/hash/RabinKarp.h"
namespace py = pybind11;
using namespace std;


std::string strip_malformed_utf8(const std::string &s, int &start, int &stop)
{
	int size = s.size();
	while (start < size && !TextC::utf8ByteSize(s[start]))
		++start;
    int utf8ByteSize = TextC::utf8ByteSize(s[stop - 1]);
    if (utf8ByteSize) {
        if (utf8ByteSize > 1)
            --stop;
    }
    else {
        int next_utf8ByteSize = stop < size? TextC::utf8ByteSize(s[stop]) : 1;
        if (!next_utf8ByteSize) {
            while (stop && !TextC::utf8ByteSize(s[stop]))
                --stop;
        }
    }
	return s.substr(start, max(stop - start, 0));
}

py::list repetition_penalty(py::str py_str)
{
    // Convert Python str to UTF-8 encoded string
    string text = py_str.cast<string>();
    // Detect redundant patterns in the text
    py::list list;
    RabinKarp parser(text);
    parser.init_physicOffset();
    for (auto &[scan_length, hashCode, indices] : parser.redundancy_detect())
    {
        int start = indices[0];
        int stop = start + scan_length;
        auto error = strip_malformed_utf8(text, start, stop);
        int offset = start - indices[0];
        if (offset) {
            for (int &index : indices)
                index += offset;
        }
        py::dict obj;
        obj["text"] = error;
        obj["index"] = parser.physic2logic(indices);
        obj["scan_length"] = stop - start;
        list.append(obj);
    }
    return list;
}

// Binding the function to Python
PYBIND11_MODULE(rabin_karp, m)
{
    m.def("repetition_penalty", &repetition_penalty);
}