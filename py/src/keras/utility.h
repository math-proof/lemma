#pragma once
#include "../std/utility.h"
#include <omp.h>
//#define EIGEN_HAS_OPENMP
//#define EIGEN_DONT_PARALLELIZE
//#define EIGEN_USE_MKL_ALL
#include "../Eigen/Dense"

using floatx = double;

using Vector = Eigen::Matrix<double, 1, -1, 1>;
using Matrix = Eigen::Matrix<double, -1, -1, 1>;
using Tensor = vector<Matrix>;
using Array4 = vector<Tensor>;

using VectorI = vector<int>;
using MatrixI = vector<VectorI>;
using TensorI = vector<MatrixI>;
using Array4I = vector<TensorI>;

using VectorD = vector<double>;
using MatrixD = vector<VectorD>;
using TensorD = vector<MatrixD>;
using Array4D = vector<TensorD>;

using VectorF = vector<float>;
using MatrixF = vector<VectorF>;
using TensorF = vector<MatrixF>;

VectorD convert2vector(const Matrix &m, int row_index);
VectorD convert2vector(const Vector &m);
MatrixD convert2vector(const Matrix &m);

VectorI string2id(const String &s, const dict<char16_t, int> &dict);
VectorI string2id(const vector<String> &s, const dict<String, int> &dict);

VectorI string2id(const vector<string> &s, const dict<string, int> &dict);
MatrixI string2id(const vector<String> &s, const dict<char16_t, int> &dict);

MatrixI string2id(const vector<vector<String>> &s,
		const dict<String, int> &dict);

//forward declaration to prevent runtime linking error.
extern string workingDirectory;
extern string testingDirectory;
string assetsDirectory();

#pragma GCC diagnostic ignored "-Wattributes"
//warning: optimization attribute on 'std::ostream& operator<<(std::ostream&, const slice&)' follows definition but the attribute doesn't match [-Wattributes]

enum class Language : int {
	en, cn, jp, de, fr
};

BinaryFile& operator >>(BinaryFile&lhs, double &a);
BinaryFile& operator >>(BinaryFile&lhs, Vector &arr);
BinaryFile& operator >>(BinaryFile&lhs, Matrix &arr);
BinaryFile& operator >>(BinaryFile&lhs, Tensor &arr);

extern const double PI;
