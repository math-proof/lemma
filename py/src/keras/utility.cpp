#include "utility.h"

#include <string>
#include<fstream>

using namespace std;

string workingDirectory = "../";
string testingDirectory = "../";

string assetsDirectory(){
	return workingDirectory + "assets/";
}

VectorD convert2vector(const Matrix &m, int row_index) {
	auto start = m.data() + row_index * m.cols();

	VectorD v(start, start + m.cols());
	return v;
}

MatrixD convert2vector(const Matrix &m) {
	MatrixD v(m.rows(), VectorD(m.cols(), 0.0));
	for (int i = 0; i < m.rows(); ++i) {
		for (int j = 0; j < m.cols(); ++j) {
			v[i][j] = m(i, j);
		}
	}
	return v;
}

VectorD convert2vector(const Vector &m) {
	auto start = m.data();

	VectorD v(start, start + m.cols());
	return v;
}

const int UNK = 1;
VectorI string2id(const String &s, const ::dict<char16_t, int> &dict) {
	VectorI v(s.size());

	for (size_t i = 0; i < s.size(); ++i) {
		auto iter = dict.find(s[i]);
		v[i] = iter == dict.end() ? UNK : iter->second;
	}
	return v;
}

MatrixI string2id(const vector<String> &s, const ::dict<char16_t, int> &dict) {
	MatrixI v(s.size());

	for (size_t i = 0; i < s.size(); ++i) {
		v[i] = string2id(s[i], dict);
	}
	return v;
}

MatrixI string2id(const vector<vector<String>> &s,
		const ::dict<String, int> &dict) {
	MatrixI v(s.size());

	for (size_t i = 0; i < s.size(); ++i) {
		v[i] = string2id(s[i], dict);
	}
	return v;
}

VectorI string2id(const vector<String> &s, const ::dict<String, int> &dict) {
	VectorI v(s.size());

	for (size_t i = 0; i < s.size(); ++i) {
		auto iter = dict.find(s[i]);
		v[i] = iter == dict.end() ? UNK : iter->second;
	}
	return v;
}

VectorI string2id(const vector<string> &s, const ::dict<string, int> &dict) {
	VectorI v(s.size());

	for (size_t i = 0; i < s.size(); ++i) {
		auto iter = dict.find(s[i]);
		v[i] = iter == dict.end() ? UNK : iter->second;
	}
	return v;
}


#include <omp.h>
#include <iostream>
//int cpu_count = []() -> int {
////	http://eigen.tuxfamily.org/dox/TopicMultiThreading.html
//		int cpu_count = omp_get_max_threads();
//		Eigen::setNbThreads(cpu_count);
//		Eigen::initParallel();
//		cout << "Eigen::initParallel() is called!" << endl;
//		cout << "cpu_count = " << cpu_count << endl;
//		return cpu_count;
//	}();

#include <chrono>
//gcc -mavx -mfma
void test_speed() {
	const int dim = 100;
	std::chrono::time_point<std::chrono::system_clock> start, end;

	int n;
	n = Eigen::nbThreads();
	cout << n << "\n";

	Matrix m1(dim, dim);
	Matrix m2(dim, dim);
	Matrix m_res(dim, dim);
	m1.setRandom(dim, dim);
	m2.setRandom(dim, dim);

	start = std::chrono::system_clock::now();

	for (int i = 0; i < 100000; ++i) {
		m_res = m1 * m2;
	}

	end = std::chrono::system_clock::now();
	std::chrono::duration<double> elapsed_seconds = end - start;

	std::cout << "elapsed time: " << elapsed_seconds.count() << "s\n";
}

//http://eigen.tuxfamily.org/dox/
//https://blog.csdn.net/zong596568821xp/article/details/81134406
void test_eigen() {
	Matrix A = Matrix::Random(3000, 3000);  // 随机初始化矩阵
	Matrix B = Matrix::Random(3000, 3000);

	double start = clock();
	Matrix C = A * B;    // 乘法好简洁
	double endd = clock();
	double thisTime = (double) (endd - start) / CLOCKS_PER_SEC;

	cout << "time cost for 3000 * 3000 matrix multiplication: = " << thisTime
			<< endl;
}

const double PI = atan(1) * 4;

extern "C" {
void initialize_working_directory(const char *_workingDirectory) {
	Timer timer(__PRETTY_FUNCTION__);
	workingDirectory = _workingDirectory;
	append_file_separator(workingDirectory);
	if (workingDirectory[0] == '~') {
		workingDirectory = getenv("HOME") + workingDirectory.substr(1);
	}

	cout << "after initializing workingDirectory = " << workingDirectory
			<< endl;
}
}
