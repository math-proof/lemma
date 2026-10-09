#include <math.h>
#include "matrix.h"
#include "../std/lagacy.h"

Vector& aggregate(const Matrix &x, Vector &v, vector<int> &arg,
		double (Matrix::ConstRowXpr::*aggregate)(int*) const) {
	int m = x.rows();
	v.resize(m);
	arg.resize(m);
	for (int i = 0; i < m; ++i) {
		v[i] = (x.row(i).*aggregate)(&arg[i]);
	}
	return v;
}

Vector& max(const Matrix &x, Vector &max, vector<int> &argmax) {
	return aggregate(x, max, argmax, &Matrix::ConstRowXpr::maxCoeff);
}

Vector& min(const Matrix &x, Vector &min, vector<int> &argmin) {
	return aggregate(x, min, argmin, &Matrix::ConstRowXpr::minCoeff);
}

int max(const vector<int> &x, int &index) {
	int max = std::numeric_limits<int>::min();
	for (int i = 0, size = x.size(); i < size; ++i) {
		if (x[i] > max) {
			max = x[i];
			index = i;
		}
	}
	return max;
}

int max(const vector<int> &x) {
	int index;
	return max(x, index);
}

Vector max(const Matrix &x) {
	Vector y;
	vector<int> argmax;
	return max(x, y, argmax);
}

Vector min(const Matrix &x) {
	Vector y;
	vector<int> argmax;
	return min(x, y, argmax);
}
//eigen.tuxfamily.org/dox/TopicFunctionTakingEigenTypes.html
//http://eigen.tuxfamily.org/dox/group__TutorialMapClass.html
//https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#abstract

//double hard_sigmoid(double x) {
//	if (x < -2.5)
//		return 0;
//	if (x > 2.5)
//		return 1;
//	return 0.2 * x + 0.5;
//}
//

double elu(double x, double alpha) {
	if (x >= 0)
		return x;
	return alpha * (exp(x) - 1);
}

double elu(double x) {
	if (x >= 0)
		return x;
	return exp(x) - 1;
}

//double relu(double x) {
//	return x < 0 ? 0 : x;
//}
//
double inverse(double x) {
	return 1 / x;
}

double sigmoid(double x) {
	return 1 / (1 + exp(-x));
}

Vector& apply(Vector &x, double (*fptr)(double)) {
	int cols = x.cols();

	for (int j = 0; j < cols; ++j) {
		x[j] = fptr(x[j]);
	}
	return x;
}

Matrix& apply(Matrix &x, double (*fptr)(double)) {
	int rows = x.rows();
	int cols = x.cols();

	for (int i = 0; i < rows; ++i) {
		for (int j = 0; j < cols; ++j) {
			x(i, j) = fptr(x(i, j));
		}
	}
	return x;
}

vector<Vector>& apply(vector<Vector> &x, double (*fptr)(double)) {
	int batch_size = x.size();

	for (int k = 0; k < batch_size; ++k) {
		apply(x[k], fptr);
	}
	return x;
}

Tensor& apply(Tensor &x, double (*fptr)(double)) {
	int batch_size = x.size();

	for (int k = 0; k < batch_size; ++k) {
		apply(x[k], fptr);
	}
	return x;
}

Matrix& sigmoid(Matrix &x) {
	return apply(x, sigmoid);
}

Tensor& sigmoid(Tensor &x) {
	return apply(x, sigmoid);
}

Vector& sigmoid(Vector &x) {
	return apply(x, sigmoid);
}

vector<Vector>& sigmoid(vector<Vector> &x) {
	return apply(x, sigmoid);
}

Matrix& hard_sigmoid(Matrix &x) {
	return apply(x, hard_sigmoid);
}

Tensor& hard_sigmoid(Tensor &x) {
	return apply(x, hard_sigmoid);
}

Vector& hard_sigmoid(Vector &x) {
	return apply(x, hard_sigmoid);
}

vector<Vector>& hard_sigmoid(vector<Vector> &x) {
	return apply(x, hard_sigmoid);
}

Matrix& tanh(Matrix &x) {
	return apply(x, std::tanh);
}

Tensor& tanh(Tensor &x) {
	return apply(x, std::tanh);
}

Vector& tanh(Vector &x) {
	return apply(x, std::tanh);
}

vector<Vector>& tanh(vector<Vector> &x) {
	return apply(x, std::tanh);
}

Tensor& exp(Tensor &x) {
	return apply(x, std::exp);
}

Matrix& exp(Matrix &x) {
	return apply(x, std::exp);
}

Vector& exp(Vector &x) {
	return apply(x, std::exp);
}

vector<Vector>& exp(vector<Vector> &x) {
	return apply(x, std::exp);
}

int relu(int x) {
	return std::max(x, 0);
}

Matrix& relu(Matrix &x) {
	return apply(x, relu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

Tensor& relu(Tensor &x) {
	return apply(x, relu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

Vector& relu(Vector &x) {
	return apply(x, relu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

vector<Vector>& relu(vector<Vector> &x) {
	return apply(x, relu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

Matrix& elu(Matrix &x) {
	return apply(x, elu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

Tensor& elu(Tensor &x) {
	return apply(x, elu);
}

Vector& elu(Vector &x) {
	return apply(x, elu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

vector<Vector>& elu(vector<Vector> &x) {
	return apply(x, elu);
//	return x.cwiseProduct((x.array() > 0.0).matrix().cast<double>());
}

vector<Vector>& gelu(vector<Vector> &x) {
	return apply(x, gelu);
}

Matrix& gelu(Matrix &x) {
	return apply(x, gelu);
}

Vector& gelu(Vector &x) {
	return apply(x, gelu);
}

Tensor& gelu(Tensor &x) {
	return apply(x, gelu);
}

Matrix& log_softmax(Matrix &x) {
	for (int i = 0, size = x.rows(); i < size; ++i) {
		Vector row = x.row(i);
		x.row(i) = log_softmax(row);
	}

	return x;
}

Tensor& log_softmax(Tensor &x) {
	for (int i = 0, size = x.size(); i < size; ++i) {
		log_softmax(x[i]);
	}
	return x;
}

vector<Vector>& log_softmax(vector<Vector> &x) {
	for (int i = 0, size = x.size(); i < size; ++i) {
		log_softmax(x[i]);
	}
	return x;
}

double logsumexp(Vector &x) {
	double lambda = x.maxCoeff();
	x -= lambda;
	return lambda + log(exp(x).sum());
}

Vector logsumexp(const Matrix &x) {
	int n = x.rows();
	Vector vec(n);
	for (int i = 0; i < n; ++i){
		Vector xi = x.row(i);
		vec(i) = logsumexp(xi);
	}
	return vec;
}

//log softmax(x) = x - max(x) - logsumexp(x - max(x))
Vector& log_softmax(Vector &x) {
	double lambda = x.maxCoeff();
	x -= lambda;
	Vector _x = x;
	return x - log(exp(_x).sum());
}

Matrix& softmax(Matrix &x) {
	int rows = x.rows();

	x = exp(hadamard_sub(x, max(x)));
	for (int i = 0; i < rows; ++i) {
		x.row(i) /= x.row(i).sum();
	}
	return x;
}

Tensor& softmax(Tensor &x) {
	int batch_size = x.size();

	for (int k = 0; k < batch_size; ++k) {
		softmax(x[k]);
	}
	return x;
}

vector<Vector>& softmax(vector<Vector> &x) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		softmax(x[k]);
	}
	return x;
}

Vector& softmax(Vector &x) {
	x = exp(x -= x.maxCoeff());
	x /= x.sum();
	return x;
}

Matrix& l2_normalize(Matrix &x) {
	int rows = x.rows();

	for (int i = 0; i < rows; ++i) {
		x.row(i) /= x.row(i).norm();
	}
	return x;
}

Vector& l2_normalize(Vector &x) {
	x /= x.norm();
	return x;
}

Matrix& inverse(Matrix &x) {
	return apply(x, inverse);
}

Vector& inverse(Vector &x) {
	return apply(x, inverse);
}

MatrixI& operator !=(MatrixI &x, int y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = x[k] != y;
	}

	return x;
}

VectorI& operator !=(VectorI &x, int y) {
	int cols = x.size();
	for (int j = 0; j < cols; ++j) {
		x[j] = x[j] != y;
	}

	return x;
}

MatrixI& operator ==(MatrixI &x, int y) {
	int rows = x.size();
	int cols = x[0].size();

	for (int i = 0; i < rows; ++i) {
		for (int j = 0; j < cols; ++j) {
			x[i][j] = x[i][j] == y ? 1 : 0;
		}
	}
	return x;
}

vector<Vector> mean(const Tensor &x) {
	vector<Vector> mean;
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		mean[k] = x[k].rowwise().mean();
	}
	return mean;
}

Vector mean(const Matrix &x) {
	Vector mean;
	mean = x.rowwise().mean();

	return mean;
}

VectorD mean(const vector<Vector> &x) {
	VectorD mean;
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		mean[k] = x[k].mean();
	}
	return mean;
}

Tensor& operator -(Tensor &x, const vector<Vector> &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] -= y[k];
	}
	return x;
}

Tensor& square(Tensor &x) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = x[k].array().square();
	}
	return x;
}

Matrix& square(Matrix &x) {
	x = x.array().square();

	return x;
}

Vector& square(Vector &x) {
	x = x.array().square();
	return x;
}

vector<Vector>& square(vector<Vector> &x) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = x[k].array().square();
	}
	return x;
}

vector<Vector>& sqrt(vector<Vector> &x) {
	return apply(x, sqrt);
}

Matrix& sqrt(Matrix &x) {
	return apply(x, sqrt);
}

Vector& sqrt(Vector &x) {
	return apply(x, sqrt);
}

VectorD& sqrt(VectorD &x) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = sqrt(x[k]);
	}
	return x;
}

Tensor& operator +=(Tensor &x, const Vector &y) {
	const auto &y_array = y.array();
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		int rows = x[k].rows();
		for (int j = 0; j < rows; ++j) {
			x[k].row(j).array() += y_array;
		}
	}
	return x;
}

Tensor& operator +=(Tensor &x, const Matrix &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] += y;
	}
	return x;
}

Tensor& operator +=(Tensor &x, const Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] += y[k];
	}
	return x;
}

vector<Vector>& operator +=(vector<Vector> &x, double y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k].array() += y;
	}
	return x;
}

VectorD& operator +=(VectorD &x, double y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] += y;
	}
	return x;

}

vector<Vector>& operator +=(vector<Vector> &x, const Vector &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] += y;
	}
	return x;
}

vector<Vector>& operator +=(vector<Vector> &x, const vector<Vector> &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] += y[k];
	}
	return x;
}

Matrix& operator +=(Matrix &x, double y) {
	x.array() += y;
	return x;
}

Vector& operator +=(Vector &x, double y) {
	x.array() += y;
	return x;
}

MatrixI& operator -(int x, MatrixI &y) {
	int rows = y.size();
	int cols = y[0].size();
	for (int i = 0; i < rows; ++i) {
		for (int j = 0; j < cols; ++j) {
			y[i][j] = x - y[i][j];
		}
	}

	return y;
}

Matrix& operator -(double x, Matrix &y) {
	for (int i = 0, size = y.size(); i < size; ++i) {
		y(i) = x - y(i);
	}

	return y;
}

MatrixI& operator -=(MatrixI &x, int y) {

	int rows = x.size();
	for (int i = 0; i < rows; ++i) {
		x[i] -= y;
	}

	return x;
}

MatrixI& operator +=(MatrixI &x, int y) {

	int rows = x.size();
	for (int i = 0; i < rows; ++i) {
		x[i] += y;
	}

	return x;
}

VectorI& operator +=(VectorI &x, const VectorI &y) {

	int rows = x.size();
	for (int i = 0; i < rows; ++i) {
		x[i] += y[i];
	}

	return x;
}

MatrixI& operator +=(MatrixI &x, const MatrixI &y) {

	int rows = x.size();
	for (int i = 0; i < rows; ++i) {
		x[i] += y[i];
	}

	return x;
}

VectorI& operator -=(VectorI &x, int y) {
	for (int &t : x) {
		t -= y;
	}

	return x;
}

Vector& operator -=(Vector &x, double y) {
	x.array() -= y;
	return x;
}

Vector& operator -(Vector &x, double y) {
	return x -= y;
}

Tensor& operator -=(Tensor &x, const vector<Vector> &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		int rows = x[k].rows();
		for (int j = 0; j < rows; ++j) {
			x[k].row(j) -= y[k];
		}
	}
	return x;
}

Tensor& operator -=(Tensor &x, const Matrix &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] -= y;
	}
	return x;
}

Tensor& operator -=(Tensor &x, const Tensor &y) {
	int size = x.size();
	for (int k = 0; k < size; ++k) {
		x[k] -= y[k];
	}
	return x;
}

MatrixI& operator -=(MatrixI &x, const MatrixI &y) {
	int size = x.size();
	for (int k = 0; k < size; ++k) {
		x[k] -= y[k];
	}
	return x;
}

//Matrix& operator -=(Matrix &x, const MatrixI &y) {
//	return x -= to_matrix(y);
//}

VectorI& operator -=(VectorI &x, const VectorI &y) {
	int size = x.size();
	for (int k = 0; k < size; ++k) {
		x[k] -= y[k];
	}
	return x;
}

vector<Vector>& operator -=(vector<Vector> &x, const vector<Vector> &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] -= y[k];
	}
	return x;
}

vector<Vector>& operator -=(vector<Vector> &x, const VectorD &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k].array() -= y[k];
	}
	return x;
}

//vector<Vector> operator *(double x, const MatrixI &y) {
//	vector<Vector> out;
//	int batch_size = y.size();
//	out.resize(batch_size);
//	for (int k = 0; k < batch_size; ++k) {
//		out[k] = y[k] * x;
//	}
//	return out;
//}

Tensor& operator *=(Tensor &x, const Vector &y) {
	const auto &y_array = y.array();
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		int rows = x[k].rows();
		for (int j = 0; j < rows; ++j) {
			x[k].row(j).array() *= y_array;
		}
	}
	return x;
}
//matrix multiply
Tensor& operator &=(Tensor &x, const Matrix &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] *= y;
	}
	return x;
}

vector<Vector>& operator *=(vector<Vector> &x, const Matrix &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		int rows = x[k].rows();
		for (int j = 0; j < rows; ++j) {
			x[k] *= y;
		}
	}
	return x;
}

MatrixI operator *(int y, const MatrixI &x) {
	MatrixI tmp = x;
	tmp *= y;
	return tmp;
}

MatrixI& operator *=(MatrixI &x, int y) {
	int rows = x.size();
	for (int k = 0; k < rows; ++k) {
		x[k] *= y;
	}
	return x;
}

MatrixI& operator *=(MatrixI &x, const MatrixI &y) {
	int rows = x.size();
	for (int k = 0; k < rows; ++k) {
		x[k] *= y[k];
	}
	return x;
}

VectorI& operator *=(VectorI &x, const VectorI &y) {
	int rows = x.size();
	for (int k = 0; k < rows; ++k) {
		x[k] *= y[k];
	}
	return x;
}

VectorI& operator *=(VectorI &x, int y) {
	for (auto &t : x) {
		t *= y;
	}
	return x;
}

VectorD& operator *=(VectorD &x, double y) {
	for (auto &t : x) {
		t *= y;
	}
	return x;
}

Tensor& operator /=(Tensor &x, const vector<Vector> &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		int rows = x[k].rows();
		for (int j = 0; j < rows; ++j) {
			x[k].row(j).array() /= y[k].array();
		}
	}
	return x;
}

Tensor& operator /=(Tensor &x, double y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] /= y;
	}
	return x;
}

vector<Vector>& operator /=(vector<Vector> &x, double y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] /= y;
	}
	return x;
}

vector<Vector>& operator /=(vector<Vector> &x, const VectorD &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] /= y[k];
	}
	return x;
}

template<>
Tensor& batch_dot<true>(Tensor &x, const Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] *= y[k].transpose();
	}
	return x;
}

template<>
Tensor& batch_dot<true>(const Tensor &x, Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		y[k] = x[k] * y[k].transpose();
	}
	return y;
}

template<>
Tensor& batch_dot<false>(Tensor &x, const Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] *= y[k];
	}
	return x;
}

template<>
Tensor& batch_dot<false>(const Tensor &x, Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		y[k] = x[k] * y[k];
	}
	return y;
}

template<>
vector<Vector>& batch_dot<true>(vector<Vector> &x, const Tensor &y) {
	int batch_size = x.size();

	for (int k = 0; k < batch_size; ++k) {
		x[k] *= y[k].transpose();
	}
	return x;
}

template<>
vector<Vector>& batch_dot<false>(vector<Vector> &x, const Tensor &y) {
	int batch_size = x.size();

	for (int k = 0; k < batch_size; ++k) {
		x[k] *= y[k];
	}
	return x;
}

vector<Vector>& extract(const Tensor &x, int index) {
	vector<Vector> out;
	return extract(x, index, out);
}

vector<Vector>& extract(const Tensor &x, int index, vector<Vector> &out) {
	int batch_size = x.size();
	out.resize(batch_size);

	for (int k = 0; k < batch_size; ++k) {
		out[k] = x[k].row(index);
	}
	return out;
}

Matrix& hadamard_sub(Matrix &x, const Vector &y) {
	for (int i = 0; i < x.rows(); ++i) {
		x.row(i).array() -= y(i);
	}
	return x;
}

Tensor& mul(Tensor &x, const Matrix &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = x[k].cwiseProduct(y);
	}
	return x;
}

Tensor& mul(Tensor &x, const Vector &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = mul(x[k], y);
	}
	return x;
}

Tensor& mul(Tensor &x, const Tensor &y) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k) {
		x[k] = x[k].cwiseProduct(y[k]);
	}
	return x;
}

Matrix& hadamard_mul(Matrix &x, const Vector &y) {
	for (int i = 0; i < x.rows(); ++i) {
		x.row(i).array() *= y(i);
	}
	return x;
}

Matrix& hadamard_mul(Matrix &x, const VectorI &y) {
	for (int i = 0; i < x.rows(); ++i) {
		x.row(i).array() *= y[i];
	}
	return x;
}

Matrix& hadamard_div(Matrix &x, const Vector &y) {
	for (int i = 0; i < x.rows(); ++i) {
		x.row(i).array() /= y(i);
	}
	return x;
}

Matrix& hadamard_add(Matrix &x, const Vector &y) {
	for (int i = 0; i < x.rows(); ++i) {
		x.row(i).array() += y(i);
	}
	return x;
}

Matrix& sub(Matrix &x, const Vector &y) {
	x.rowwise() -= y;
	return x;
}

Matrix& mul(Matrix &x, const Vector &y) {
	x.array().rowwise() *= y.array();
	return x;
}

Vector& mul(Vector &x, const Vector &y) {
	x.array() *= y.array();
	return x;
}

Matrix& mul(Matrix &x, const Matrix &y) {
	x.array() *= y.array();
	return x;
}

Matrix& div(Matrix &x, const Vector &y) {
	x.array().rowwise() /= y.array();
	return x;
}

Matrix& add(Matrix &x, const Vector &y) {
	x.rowwise() += y;
	return x;
}

Matrix add(const Matrix &_x, const Vector &y) {
	auto x = _x;
	return add(x, y);
}

Matrix dot(const Tensor &x, const Tensor &y) {
	Matrix z;
	int n = x.size();
	int m = x[0].rows();
	z.resize(n, m);

	for (int i = 0; i < n; ++i)
		for (int j = 0; j < m; ++j) {
			z(i, j) = x[i].row(j) * y[i].row(j).transpose();
		}

	return z;
}

Tensor& numpify(Tensor &tensor) {
	int rows = 0;
	int cols = 0;
	for (Matrix &mat : tensor) {
		if (mat.rows() > rows)
			rows = mat.rows();
		if (mat.cols() > cols)
			cols = mat.cols();
	}

	for (Matrix &mat : tensor) {
		int old_rows = mat.rows();
		int old_cols = mat.cols();
		if (old_rows != rows || old_cols != cols) {
			Matrix old_mat = mat;
			mat.resize(rows, cols);
			for (int i = 0; i < old_rows; ++i) {
				for (int j = 0; j < old_cols; ++j) {
					mat(i, j) = old_mat(i, j);
				}
			}
		}
	}

	return tensor;
}

MatrixI& numpify(MatrixI &matrix, Padding padding) {
//	Timer timer(__PRETTY_FUNCTION__);
	int cols = 0;
	for (const VectorI &v : matrix) {
		if (v.size() > cols)
			cols = v.size();
	}

	for (VectorI &v : matrix) {
		int diff = cols - v.size();
		if (diff > 0) {
			if (padding == Padding::tailing) {
				v.resize(cols);
			} else {
				v.insert(v.begin(), diff, 0);
			}
		}
	}

//	print(cols);
	return matrix;
}

Matrix broadcast(const Vector &x, int rows) {
	Matrix ret;
	ret.resize(rows, x.cols());
	for (int i = 0; i < rows; ++i) {
		ret.row(i) = x;
	}
	return ret;
}

Matrix broadcast(const Eigen::Block<Matrix, 1, -1, 1> &x, int rows) {
	Matrix ret;
	ret.resize(rows, x.cols());
	for (int i = 0; i < rows; ++i) {
		ret.row(i) = x;
	}
	return ret;
}

Matrix broadcast(const Eigen::Block<const Matrix, 1, -1, 1> &x, int rows) {
	Matrix ret;
	ret.resize(rows, x.cols());
	for (int i = 0; i < rows; ++i) {
		ret.row(i) = x;
	}
	return ret;
}

template<>
Tensor transpose<0, 2, 1>(const Tensor &x) {
	int n = x.size();
	Tensor y(n);
	for (int i = 0; i < n; ++i)
		y[i] = x[i].transpose();
	return y;
}

Tensor& transposeInPlace(Tensor &x) {
	int batch_size = x.size();
	for (int k = 0; k < batch_size; ++k)
		x[k].transposeInPlace();
	return x;
}

template<>
Tensor transpose<2, 0, 1>(const Tensor &x) {
//	Timer timer(__PRETTY_FUNCTION__);
	int n = x.size();
	int m = x[0].rows();
	int z_dimension = x[0].cols();

	Tensor y = random_array(z_dimension, n, m);
	for (int z = 0; z < z_dimension; ++z) {
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < m; ++j) {
				y[z](i, j) = x[i](j, z);
			}
		}
	}
	return y;
}

template<>
Tensor transpose<2, 1, 0>(const Tensor &x) {
	int n = x.size();
	int m = x[0].rows();
	int z_dimension = x[0].cols();
	Tensor y = random_array(z_dimension, m, n);
	for (int z = 0; z < z_dimension; ++z) {
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < m; ++j) {
				y[z](j, i) = x[i](j, z);
			}
		}
	}
	return y;
}

MatrixI& transpose(MatrixI &mat) {
	int rows = mat.size();
	int cols = mat[0].size();
	if (rows > cols) {
		throw std::runtime_error("unimplemented");
	} else if (rows < cols) {
		throw std::runtime_error("unimplemented");
	} else {
		for (int i = 1; i < rows; ++i) {
			for (int j = 0; j < i; ++j) {
				std::swap(mat[i][j], mat[j][i]);
			}
		}
	}
	return mat;
}

MatrixI transpose(const MatrixI &mat) {
	int rows = mat.size();
	int cols = mat[0].size();
	MatrixI ret = int_zeros(cols, rows);
	for (int i = 0; i < rows; ++i) {
		for (int j = 0; j < cols; ++j) {
			ret[j][i] = mat[i][j];
		}
	}

	return ret;
}

Tensor random_array(int x_shape, int y_shape, int z_shape) {
	Tensor t(x_shape);
	for (int i = 0; i < x_shape; ++i) {
		t[i].resize(y_shape, z_shape);
	}
	return t;
}

Matrix random_array(int x_shape, int y_shape) {
	Matrix t(x_shape, y_shape);
	return t;
}

Vector random_array(int x_shape) {
	Vector t(x_shape);
	return t;
}

Vector zeros(int x_shape) {
	return constant(x_shape, 0);
}

Vector ones(int x_shape) {
	return constant(x_shape, 1);
}

Vector constant(int x_shape, double x) {
	Vector t = random_array(x_shape);
	int size = t.size();
	stosq_double(t.data(), x, size);
	return t;
}

Matrix zeros(int x_shape, int y_shape) {
	return constant(x_shape, y_shape, 0);
}

Matrix ones(int x_shape, int y_shape) {
	return constant(x_shape, y_shape, 1);
}

Matrix constant(int x_shape, int y_shape, double x) {
	auto t = random_array(x_shape, y_shape);
	int size = t.size();
	stosq_double(t.data(), x, size);
	return t;
}

Tensor zeros(int x_shape, int y_shape, int z_shape) {
	return constant(x_shape, y_shape, z_shape, 0);
}

Tensor ones(int x_shape, int y_shape, int z_shape) {
	return constant(x_shape, y_shape, z_shape, 1);
}

Tensor constant(int x_shape, int y_shape, int z_shape, double x) {
	auto t = random_array(x_shape, y_shape, z_shape);
	for (auto &mat : t) {
		stosq_double(mat.data(), x, mat.size());
	}
	return t;
}

MatrixI int_zeros(int m, int n) {
	return array_of_zeros<int>(m, n);
}

MatrixI int_ones(int m, int n) {
	MatrixI x(m);
	for (auto &v : x) {
		v.assign(n, 1);
	}
	return x;
}

VectorD compress(const double *begin, const double *end, int compress_size) {
//	Timer timer(__PRETTY_FUNCTION__);

	int size = (end - begin) / compress_size;
	VectorD newV(size);
	for (int i = 0; i < size; ++i) {
//		newV[i] = sum(begin + i * compress_size, begin + (i + 1) * compress_size);
		newV[i] = begin[i * compress_size];
	}
	return newV;

}

MatrixI argmax(const Tensor &energy, int dim) {
	Matrix scores;
	return argmax(energy, scores, dim);
}

MatrixI argmax(const Tensor &energy, Matrix &scores, int dim) {
	if (dim == 0) {
		int dep_tag_num = energy.size();
		int seq_length = energy[0].cols();
		scores.resize(seq_length, seq_length);
		MatrixI argmax = int_zeros(seq_length, seq_length);
		for (int j = 0; j < seq_length; ++j) {
			for (int i = 0; i < seq_length; ++i) {
				double m = -oo;
				int index = -1;
				for (int k = 0; k < dep_tag_num; ++k) {
					auto _m = energy[k](i, j);
					if (_m > m) {
						m = _m;
						index = k;
					}
				}

				scores(i, j) = m;
				argmax[i][j] = index;
			}
		}
		return argmax;
	}

	throw std::runtime_error("unimplemented");
}

VectorI argmin(const Matrix &energy, int dim) {
	if (dim == 1 || dim == -1) {
		int seq_length = energy.rows();

		int cols = energy.cols();

		VectorI argmin(seq_length);

		for (int i = 0; i < seq_length; ++i) {
			double m = oo;
			int index = -1;
			for (int j = 0; j < cols; ++j) {
				auto _m = energy(i, j);
				if (_m < m) {
					m = _m;
					index = j;
				}
			}

			argmin[i] = index;
		}

		return argmin;
	}

	throw std::runtime_error("unimplemented");
}

VectorI argmax(const Matrix &energy, int dim) {
//	Timer timer(__PRETTY_FUNCTION__);
	if (dim == 1 || dim == -1) {
		int rows = energy.rows();

		int cols = energy.cols();

		VectorI argmax(rows);

		for (int i = 0; i < rows; ++i) {
			double m = -oo;
			int index = -1;
			for (int j = 0; j < cols; ++j) {
				auto _m = energy(i, j);
				if (_m > m) {
					m = _m;
					index = j;
				}
			}

			argmax[i] = index;
		}

//		print(argmax);
		return argmax;
	}

	throw std::runtime_error("unimplemented");
}

VectorI& operator +=(VectorI &x, int y) {
	for (auto &e : x) {
		e += y;
	}
	return x;
}

Vector operator *(const VectorI &x, double y) {
	Vector out;
	int size = x.size();
	out.resize(size);

	for (int i = 0; i < size; ++i) {
		out[i] = x[i] * y;
	}

	return out;
}

MatrixI& clip(MatrixI &x, int min, int max) {
	int rows = x.size();
	for (int i = 0; i < rows; ++i) {
		clip(x[i], min, max);
	}
	return x;

}

int clip(int x, int min, int max) {
	if (x > max) {
		x = max;
	}
	if (x < min) {
		x = min;
	}
	return x;
}

VectorI& clip(VectorI &x, int min, int max) {
	int size = x.size();
	for (int i = 0; i < size; ++i) {
		auto &ref = x[i];
		ref = clip(ref, min, max);
	}
	return x;

}

TensorD to_double_vector(const Tensor &A) {
	int size = A.size();
	TensorD B(size);
	for (int i = 0; i < size; ++i) {
		B[i] = to_double_vector(A[i]);
	}
	return B;
}

Array4D to_double_vector(const vector<Tensor> &A) {
	int size = A.size();
	Array4D B(size);
	for (int i = 0; i < size; ++i) {
		B[i] = to_double_vector(A[i]);
	}
	return B;
}

MatrixD to_double_vector(const Matrix &A) {

	int n = A.rows();
	int m = A.cols();
	MatrixD matrix(n);

	for (int i = 0; i < n; ++i) {
		matrix[i].resize(m);
		for (int j = 0; j < m; ++j) {
			matrix[i][j] = A(i, j);
		}
	}
	return matrix;
}

VectorD to_double_vector(const Vector &A) {

	int n = A.size();
	VectorD vec(n);

	for (int i = 0; i < n; ++i) {
		vec[i] = A[i];
	}
	return vec;
}

VectorI& strip_tailing_zeros(VectorI &input_ids) {
	int valid_len = input_ids.size();
	for (int i = valid_len - 1; i >= 0; --i) {
		if (input_ids[i])
			break;
		else
			--valid_len;
	}

	input_ids.resize(valid_len);
	return input_ids;
}

MatrixI& strip_tailing_zeros(MatrixI &input_ids) {

	for (auto &v : input_ids) {
		strip_tailing_zeros(v);
	}
	return input_ids;
}

TensorI& strip_tailing_zeros(TensorI &input_ids) {
	for (auto &v : input_ids) {
		strip_tailing_zeros(v);
	}
	return input_ids;
}

Matrix& cast_to_floats(Matrix &x) {
	return apply(x, [](double x) {
		return (double) (float) x;
	});
}


MatrixI& cast_to_bool(MatrixI &x) {
	auto rows = x.size();
	auto cols = x[0].size();
	for (size_t i = 0; i < rows; ++i){
		for (size_t j = 0; j < cols; ++j){
			x[i][j] = x[i][j]? 1 : 0;
		}
	}
	return x;
}

//https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part
Matrix& linalg_band_part(Matrix &input, int num_lower, int num_upper) {
	int m = input.rows();
	int n = input.cols();
	if (num_lower >= 0) {
		for (int i = num_lower + 1; i < m; ++i) {
			for (int j = 0; j + num_lower < i; ++j) {
				input(i, j) = 0;
			}
		}
	}

	if (num_upper >= 0) {
		for (int j = num_upper + 1; j < n; ++j) {
			for (int i = 0; i + num_upper < j; ++i) {
				input(i, j) = 0;
			}
		}
	}

	return input;
}

MatrixI& linalg_band_part(MatrixI &input, int num_lower, int num_upper) {
	int m = input.size();
	int n = input[0].size();
	if (num_lower >= 0) {
		for (int i = num_lower + 1; i < m; ++i) {
			for (int j = 0; j + num_lower < i; ++j) {
				input[i][j] = 0;
			}
		}
	}

	if (num_upper >= 0) {
		for (int j = num_upper + 1; j < n; ++j) {
			for (int i = 0; i + num_upper < j; ++i) {
				input[i][j] = 0;
			}
		}
	}

	return input;
}

//dict[i] = j;
void setitem(MatrixI &dict, int i, int j) {
	auto &v = dict[i];
	stosd(v.data(), 0, v.size());
	if (j >= 0)
		v[j] = 1;
}

//return dict[i];
int getitem(const MatrixI &dict, int i) {
	auto &v = dict[i];
	const int *begin = v.data();
	int size = v.size();
	const int *ptr = (const int*) repe_scasd(begin, 0, size);
	int offset = ptr - begin;
	if (offset >= size)
		return -1;
	return offset;
}

Matrix& gather(const Matrix &embeddings, const VectorI &inputs,
		Matrix &output) {
	int length = inputs.size();

	output.resize(length, embeddings.cols());

	for (int j = 0; j < length; ++j) {
		output.row(j) = embeddings.row(inputs[j]);
	}
	return output;
}

Matrix getitem(const Matrix &embeddings, const range &inputs) {
	int length = inputs.size();
	Matrix output;
	output.resize(length, embeddings.cols());

	for (int j = 0; j < length; ++j) {
		output.row(j) = embeddings.row(inputs[j]);
	}
	return output;
}

Tensor getitem(const Tensor &embeddings, const range &index) {
	Tensor result(index.size());
	int j = 0;
//	for (int i : index) {
//		result[j++] = embeddings[i];
//	}

	for (int i = index.start; i < index.stop; ++i) {
		result[j++] = embeddings[i];
	}

	return result;
}

//notice that inputs might not be a rectangular matrix!
Tensor gather(const Matrix &embeddings, const MatrixI &inputs) {
	int batch_size = inputs.size();

	Tensor output(batch_size);

	for (int k = 0; k < batch_size; ++k) {
		gather(embeddings, inputs[k], output[k]);
	}
	return output;
}

VectorI& assign(VectorI &lhs, const VectorI &rhs) {
	int size = rhs.size();
	if (lhs.capacity() < size) {
		throw std::runtime_error(
				"illegal to change memory allocation for C++ data instantiated from python");
	}

//	lhs.assign(rhs.begin(), rhs.end());

	lhs.resize(size);
	movsd(lhs.data(), rhs.data(), size);

	return lhs;
}

//void batch_write(vector<Tensor> &result, const Tensor &tensor) {
//	int bucket_size = tensor.size();
//	if (result.empty()) {
//		result.resize(bucket_size);
//	}
//
//	for (int i = 0; i < bucket_size; ++i) {
//		result[i].push_back(tensor[i]);
//	}
//}

Matrix concat(const Matrix &x, const Matrix &y, int axis) {
	int rows, cols;
	if (axis == 0) {
		rows = x.rows() + y.rows();
		cols = x.cols();
	} else {
		rows = x.rows();
		cols = x.cols() + y.cols();
	}

	Matrix result(rows, cols);
	result << x, y;
	return result;
}

BinaryFile& operator >>(BinaryFile &lhs, double &a) {
	Timer timer(__PRETTY_FUNCTION__);
	float _a;
	lhs >> _a;
	a = _a;
	return lhs;
}

BinaryFile& operator >>(BinaryFile &lhs, Vector &arr) {
//	Timer timer(__PRETTY_FUNCTION__);
	int n;
	lhs >> n;
	cout << "shape = (" << n << ", )" << endl;
	vector<float> v(n);
	lhs >> v;
	arr = to_vector(v);
	return lhs;
}

BinaryFile& operator >>(BinaryFile &lhs, Matrix &arr) {
//	Timer timer(__PRETTY_FUNCTION__);
	int m, n;
	lhs >> m >> n;
	cout << "shape = (" << m << ", " << n << ")" << endl;
	vector<vector<float>> mat(m);
	for (auto &v : mat) {
		v.resize(n);
	}

	lhs >> mat;
	arr = to_matrix(mat);
	return lhs;
}

BinaryFile& operator >>(BinaryFile &lhs, Tensor &arr) {
//	Timer timer(__PRETTY_FUNCTION__);
	int m, n, d;
	lhs >> m >> n >> d;
	cout << "shape = (" << m << ", " << n << ", " << d << ")" << endl;

	vector<vector<vector<float>>> tensor(m);
	for (auto &mat : tensor) {
		mat.resize(n);
		for (auto &v : mat) {
			v.resize(d);
		}
	}

	lhs >> tensor;
	arr = to_tensor(tensor);
	return lhs;

}

Matrix read_matrix(BinaryFile &lhs){
	Matrix x;
	lhs >> x;
	return x;
}

Tensor read_tensor(BinaryFile &lhs){
	Tensor x;
	lhs >> x;
	return x;
}

VectorI shape(const Matrix &x){
	return {(int)x.rows(), (int)x.cols()};
}

VectorI shape(const Tensor &x){
	int batch_size = x.size();
	int seq_length = x[0].rows();
	int embed_size = x[0].cols();

	if (batch_size > 1) {
		if (seq_length != x[1].rows() || embed_size != x[1].cols()){
			print("tensor is not a rectangular tensor!");
		}
	}

	return {batch_size, seq_length, embed_size};
}

VectorI shape(const TensorI &x){
	int batch_size = x.size();
	int seq_length = x[0].size();
	int embed_size = x[0][0].size();

	return {batch_size, seq_length, embed_size};
}

VectorI shape(const MatrixI &x){
	return {(int)x.size(), (int)x[0].size()};
}

VectorI shape(const vector<Tensor> &x){
	auto size = shape(x[0]);
	size.insert(size.begin(), x.size());
	return size;
}


Matrix middleCols(const Matrix &X, int start, int stop, int step){
	Matrix Y(X.rows(), ceiling(stop - start, step));
	int index = 0;
	for (int j : range(start, stop, step)){
		Y.col(index++) = X.col(j);
	}
	return Y;
}

Matrix middleRows(const Matrix &X, int start, int stop, int step){
	Matrix Y(ceiling(stop - start, step), X.cols());
	int index = 0;
	for (int i : range(start, stop, step)){
		Y.row(index++) = X.row(i);
	}
	return Y;
}

Vector flatten(const Matrix &x){
	int size = x.size();
	Vector vec(size);
	for (int i = 0; i < size; ++i)
		vec[i] = x(i);
	return vec;
}

Vector one_hot(int i, int size, double value){
	Vector vec = zeros(size);
	vec[i] = value;
	return vec;
}
