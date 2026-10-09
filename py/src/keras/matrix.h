#pragma once
#include "utility.h"

Vector& min(const Matrix &x, Vector &m, vector<int> &argmin);
Vector& max(const Matrix &x, Vector &m, vector<int> &argmax);

int clip(int x, int min, int max);
MatrixI& clip(MatrixI &x, int min, int max);
VectorI& clip(VectorI &x, int min, int max);

VectorI argmin(const Matrix &x, int dim = -1);
MatrixI argmin(const Tensor &x, int dim = -1);

MatrixI argmax(const Tensor &x, int dim = -1);
MatrixI argmax(const Tensor &energy, Matrix &scores, int dim = -1);
VectorI argmax(const Matrix &energy, int dim = -1);

Vector min(const Matrix &x);
Vector max(const Matrix &x);
int max(const vector<int> &x, int &index);
int max(const vector<int> &x);

Tensor& exp(Tensor &x);
Matrix& exp(Matrix &x);
Vector& exp(Vector &x);
vector<Vector>& exp(vector<Vector> &x);

Tensor& hard_sigmoid(Tensor &x);
Matrix& hard_sigmoid(Matrix &x);
Vector& hard_sigmoid(Vector &x);
vector<Vector>& hard_sigmoid(vector<Vector> &x);

Tensor& sigmoid(Tensor &x);
Matrix& sigmoid(Matrix &x);
Vector& sigmoid(Vector &x);
vector<Vector>& sigmoid(vector<Vector> &x);

Tensor& tanh(Tensor &x);
Matrix& tanh(Matrix &x);
Vector& tanh(Vector &x);
vector<Vector>& tanh(vector<Vector> &x);

//\text{ELU}(x) = \max\left(0,x\right) + \min\left(0, \alpha * \left(\exp\left(x\right) - 1\right)\right)
//https://www.codecogs.com/eqnedit.php
Tensor& elu(Tensor &x);
Matrix& elu(Matrix &x);
Vector& elu(Vector &x);
vector<Vector>& elu(vector<Vector> &x);

int relu(int x);
Tensor& relu(Tensor &x);
Matrix& relu(Matrix &x);
Vector& relu(Vector &x);
vector<Vector>& relu(vector<Vector> &x);

Matrix& gelu(Matrix &x);
Vector& gelu(Vector &x);
Tensor& gelu(Tensor &x);
vector<Vector>& gelu(vector<Vector> &x);

double logsumexp(Vector &x);
Vector logsumexp(const Matrix &x);

Matrix& log_softmax(Matrix &x);
Vector& log_softmax(Vector &x);
Tensor& log_softmax(Tensor &x);
vector<Vector>& log_softmax(vector<Vector> &x);

Matrix& softmax(Matrix &x);
Vector& softmax(Vector &x);
Tensor& softmax(Tensor &x);
vector<Vector>& softmax(vector<Vector> &x);

Matrix& l2_normalize(Matrix &f);
Vector& l2_normalize(Vector &f);

Matrix& inverse(Matrix &x);
Vector& inverse(Vector &x);

vector<Vector>& extract(const Tensor &x, int index);
vector<Vector>& extract(const Tensor &x, int index, vector<Vector> &out);

enum class Activator : int {
	linear,
	softmax,
	l2_normalize,
	relu,
	gelu,
	hard_sigmoid,
	sigmoid,
	tanh,
	elu,
	log_softmax
};

struct Activation {

	Activator act;
	template<typename _Ty>
	_Ty& operator ()(_Ty &x) const {
		switch (act) {
		case Activator::linear:
			return x;
		case Activator::softmax:
			return softmax(x);
		case Activator::log_softmax:
			return log_softmax(x);
		case Activator::relu:
			return relu(x);
		case Activator::gelu:
			return gelu(x);
		case Activator::hard_sigmoid:
			return hard_sigmoid(x);
		case Activator::sigmoid:
			return sigmoid(x);
		case Activator::tanh:
			return tanh(x);
		case Activator::elu:
			return elu(x);

		default:
			return x;
		}
	}
};

MatrixI& operator !=(MatrixI &x, int y);
MatrixI& operator ==(MatrixI &x, int y);
MatrixI& operator !=(MatrixI &x, int y);
MatrixI& operator ==(MatrixI &x, int y);
VectorI& operator !=(VectorI &x, int y);
VectorI& operator ==(VectorI &x, int y);

vector<Vector> mean(const Tensor &x);
Vector mean(const Matrix &x);
VectorD mean(const vector<Vector> &x);

Tensor& sqrt(Tensor &x);
Matrix& sqrt(Matrix &x);
Vector& sqrt(Vector &x);
vector<Vector>& sqrt(vector<Vector> &x);
VectorD& sqrt(VectorD &x);

Tensor& square(Tensor &x);
Matrix& square(Matrix &x);
Vector& square(Vector &x);
vector<Vector>& square(vector<Vector> &x);

//constant cast for short
template<typename Matrix>
const Matrix& operator +(Matrix &x) {
	return x;
}

template<typename _Tx, typename _Ty>
vector<_Tx>& operator +(vector<_Tx> &x, const _Ty &y) {
	return x += y;
}

template<typename _Tx, typename _Ty>
vector<_Tx> operator +(const vector<_Tx> &x, const _Ty &y) {
	vector<_Tx> out;
	out = x;
	return out += y;
}

template<typename _Tx, typename _Ty>
vector<_Tx>& operator -(vector<_Tx> &x, const _Ty &y) {
	return x -= y;
}

template<typename _Tx, typename _Ty>
vector<_Tx> operator -(const vector<_Tx> &x, const _Ty &y) {
	vector<_Tx> out;
	out = x;
	return out -= y;
}

template<typename _Tx, typename _Ty>
vector<_Ty> operator -(const _Tx &x, const vector<_Ty> &y) {
	vector<_Ty> out;
	out = -y;
	return out += x;
}

template<typename _Ty>
vector<_Ty> operator -(const vector<_Ty> &y) {
	int size = y.size();
	vector<_Ty> out(size);
	for (int i = 0; i < size; ++i) {
		out[i] = -y[i];
	}
	return out;
}

template<typename _Ty>
vector<_Ty>& operator -(vector<_Ty> &y) {
	int size = y.size();
	for (int i = 0; i < size; ++i) {
		y[i] = -y[i];
	}
	return y;
}

template<typename _Tx, typename _Ty>
vector<_Tx>& operator *(vector<_Tx> &x, const _Ty &y) {
	return x *= y;
}

template<typename _Tx, typename _Ty>
vector<_Tx> operator *(const vector<_Tx> &x, const _Ty &y) {
	vector<_Tx> out;
	out = x;
	return out *= y;
}

template<typename _Tx, typename _Ty>
vector<_Tx>& operator /(vector<_Tx> &x, const _Ty &y) {
	return x /= y;
}

template<typename _Tx, typename _Ty>
vector<_Tx> operator /(const vector<_Tx> &x, const _Ty &y) {
	vector<_Tx> out;
	out = x;
	return out /= y;
}

MatrixI& operator +=(MatrixI &x, int y);
MatrixI& operator +=(MatrixI &x, const MatrixI &y);
Vector& operator +=(Vector &x, double y);
Matrix& operator +=(Matrix &x, double y);
Tensor& operator +=(Tensor &x, double y);
Tensor& operator +=(Tensor &x, const Tensor &y);
vector<Vector>& operator +=(vector<Vector> &x, double y);
VectorD& operator +=(VectorD &x, double y);
VectorI& operator +=(VectorI &x, int y);
VectorI& operator +=(VectorI &x, const VectorI &y);

Tensor& operator +=(Tensor &x, const Vector &y);
Tensor& operator +=(Tensor &x, const Matrix &y);
vector<Vector>& operator +=(vector<Vector> &x, const Vector &y);
vector<Vector>& operator +=(vector<Vector> &x, const vector<Vector> &y);

Matrix& operator -(double x, Matrix &y);
MatrixI& operator -(int x, MatrixI &y);
MatrixI& operator -=(MatrixI &x, int y);
VectorI& operator -=(VectorI &x, int y);
Tensor& operator -=(Tensor &x, const vector<Vector> &y);
MatrixI& operator -=(MatrixI &x, const MatrixI &y);
//Matrix& operator -=(Matrix &x, const MatrixI &y);
VectorI& operator -=(VectorI &x, const VectorI &y);

Tensor& operator -=(Tensor &x, const Tensor &y);
Tensor& operator -=(Tensor &x, const Matrix &y);
vector<Vector>& operator -=(vector<Vector> &x, const VectorD &y);
vector<Vector>& operator -=(vector<Vector> &x, const vector<Vector> &y);
MatrixI& operator -=(MatrixI &x, int y);
Vector& operator -=(Vector &x, double y);
Vector& operator -(Vector &x, double y);

MatrixI& operator -=(MatrixI &x, int y);

//vector<Vector> operator *(double x, const MatrixI &y);
MatrixI operator *(int x, const MatrixI &y);
Tensor& operator *=(Tensor &x, const Vector &y);
Tensor& operator &=(Tensor &x, const Matrix &y);
vector<Vector>& operator *=(vector<Vector> &x, const Matrix &y);
MatrixI& operator *=(MatrixI &x, int y);
MatrixI& operator *=(MatrixI &x, const MatrixI &y);
VectorI& operator *=(VectorI &x, int y);
VectorI& operator *=(VectorI &x, const VectorI &y);
VectorD& operator *=(VectorD &x, double y);

Matrix operator *(const MatrixI &x, double y);
Vector operator *(const VectorI &x, double y);

Tensor& operator /=(Tensor &x, const Tensor &y);
Tensor& operator /=(Tensor &x, const vector<Vector> &y);
Tensor& operator /=(Tensor &x, double y);
vector<Vector>& operator /=(vector<Vector> &x, double y);
vector<Vector>& operator /=(vector<Vector> &x, const VectorD &y);

template<bool = false>
Tensor& batch_dot(Tensor &x, const Tensor &y);

template<>
Tensor& batch_dot<true>(Tensor &x, const Tensor &y);

template<>
Tensor& batch_dot<false>(Tensor &x, const Tensor &y);

template<bool = false>
Tensor& batch_dot(const Tensor &x, Tensor &y);

template<>
Tensor& batch_dot<true>(const Tensor &x, Tensor &y);

template<>
Tensor& batch_dot<false>(const Tensor &x, Tensor &y);

template<bool = false>
vector<Vector>& batch_dot(vector<Vector> &x, const Tensor &y);

template<>
vector<Vector>& batch_dot<true>(vector<Vector> &x, const Tensor &y);

template<>
vector<Vector>& batch_dot<false>(vector<Vector> &x, const Tensor &y);

Matrix& add(Matrix &x, const Vector &y);
Matrix add(const Matrix &x, const Vector &y);

Matrix& sub(Matrix &x, const Vector &y);
Matrix& div(Matrix &x, const Vector &y);

Vector& mul(Vector &x, const Vector &y);

Matrix& mul(Matrix &x, const Vector &y);
Matrix& mul(Matrix &x, const Matrix &y);

Tensor& mul(Tensor &x, const Vector &y);
Tensor& mul(Tensor &x, const Matrix &y);
Tensor& mul(Tensor &x, const Tensor &y);

Matrix& hadamard_add(Matrix &x, const Vector &y);
Matrix& hadamard_sub(Matrix &x, const Vector &y);
Matrix& hadamard_div(Matrix &x, const Vector &y);
Matrix& hadamard_mul(Matrix &x, const Vector &y);
Matrix& hadamard_mul(Matrix &x, const VectorI &y);

//precondition: x, y are of the same shape!
Matrix dot(const Tensor &x, const Tensor &y);
//Tensor& dot(const Tensor &x, const Tensor &y, Tensor &z, int z_dimension);

Tensor& numpify(Tensor &x);

enum class Padding : int {
	tailing = 0, leading = 1, valid, same, causal
};

MatrixI& numpify(MatrixI &x, Padding padding = Padding::tailing);

Matrix broadcast(const Vector &x, int rows);

Matrix broadcast(const Eigen::Block<Matrix, 1, -1, 1> &x, int rows);

Matrix broadcast(const Eigen::Block<const Matrix, 1, -1, 1> &x, int rows);

MatrixI& transpose(MatrixI &x);
MatrixI transpose(const MatrixI &x);

MatrixI outer_product(const VectorI &x, const VectorI &y);

Tensor& transposeInPlace(Tensor &x);

template<int, int, int>
Tensor transpose(const Tensor &x);

template<>
Tensor transpose<0, 2, 1>(const Tensor &x);

template<>
Tensor transpose<1, 0, 2>(const Tensor &x);

template<>
Tensor transpose<1, 2, 0>(const Tensor &x);

template<>
Tensor transpose<2, 0, 1>(const Tensor &x);

template<>
Tensor transpose<2, 1, 0>(const Tensor &x);

Tensor random_array(int x_shape, int y_shape, int z_shape);
Matrix random_array(int x_shape, int y_shape);
Vector random_array(int x_shape);

Tensor zeros(int x_shape, int y_shape, int z_shape);
Matrix zeros(int x_shape, int y_shape);
Vector zeros(int x_shape);

Tensor ones(int x_shape, int y_shape, int z_shape);
Matrix ones(int x_shape, int y_shape);
Vector ones(int x_shape);

Tensor constant(int x_shape, int y_shape, int z_shape, double value);
Matrix constant(int x_shape, int y_shape, double value);
Vector constant(int x_shape, double value);

template<typename T>
Matrix to_matrix(const vector<vector<T>> &x, int rows, int cols) {
	Matrix y(rows, cols);
	for (int i = 0; i < rows; ++i) {
		for (int j = 0; j < cols; ++j) {
			y(i, j) = x[i][j];
		}
	}
	return y;
}


template<typename T>
Matrix to_matrix(const vector<vector<T>> &x) {
	int rows = x.size();
	int cols = x[0].size();
	return to_matrix(x, rows, cols);
}

template<typename T>
Tensor to_tensor(const vector<vector<vector<T>>> &x) {
	int size = x.size();
	Tensor y(size);
	for (int i = 0; i < size; ++i) {
		y[i] = to_matrix(x[i]);
	}
	return y;
}

template<typename T>
Matrix unsqueeze(const vector<T> &x, int dim = -1, int tile = 1) {

	Matrix y;
	int rows;
	int cols;
	switch (dim) {
	case -1:
	case 1:
		rows = x.size();
		cols = tile;
		y.resize(rows, cols);

		for (int i = 0; i < rows; ++i) {
			for (int j = 0; j < cols; ++j) {
				y(i, j) = x[i];
			}
		}
		break;

	case 0:
	default:
		cols = x.size();
		rows = tile;
		y.resize(rows, cols);
		for (int i = 0; i < rows; ++i) {
			for (int j = 0; j < cols; ++j) {
				y(i, j) = x[j];
			}
		}
	}

	return y;
}

template<typename T>
Vector to_vector(const vector<T> &x) {
	Vector y;
	int n = x.size();
	y.resize(n);
	for (int i = 0; i < n; ++i) {
		y(i) = x[i];
	}
	return y;
}

MatrixI int_zeros(int m, int n);
MatrixI int_ones(int m, int n);
MatrixI Identity(int m, int n);

VectorD compress(const double *begin, const double *end, int compress_size);

VectorD to_double_vector(const Vector &x);
MatrixD to_double_vector(const Matrix &x);
TensorD to_double_vector(const Tensor &x);
Array4D to_double_vector(const vector<Tensor> &x);

VectorI& strip_tailing_zeros(VectorI &input_ids);
MatrixI& strip_tailing_zeros(MatrixI &input_ids);
TensorI& strip_tailing_zeros(TensorI &input_ids);

Matrix& cast_to_floats(Matrix &matrix);
MatrixI& cast_to_bool(MatrixI &x);

Matrix& linalg_band_part(Matrix &matrix, int num_lower, int num_upper);

MatrixI& linalg_band_part(MatrixI &matrix, int num_lower, int num_upper);

//dict[i] = j;
void setitem(MatrixI &dict, int i, int j);
//return dict[i];
int getitem(const MatrixI &dict, int i);
Matrix getitem(const Matrix &dict, const range &index);
Tensor getitem(const Tensor &dict, const range &index);

Matrix& gather(const Matrix &embeddings, const VectorI &inputs, Matrix &output);
Tensor gather(const Matrix &embeddings, const MatrixI &inputs);

VectorI& assign(VectorI &lhs, const VectorI &rhs);

//vector<Tensor> batch_write(int batch_size, Tensor (*fptr)(int));

template<typename F>
vector<Tensor> batch_write(int batch_size, F fptr) {
	vector<Tensor> result;

	for (int i = 0; i < batch_size; ++i) {
		auto tensor = fptr(i);
		int bucket_size = tensor.size();
		if (result.empty()) {
			result.resize(bucket_size);
		}

		for (int i = 0; i < bucket_size; ++i) {
			result[i].push_back(tensor[i]);
		}
	}

	for (Tensor &t : result) {
		numpify(t);
	}

	return result;
}

Matrix concat(const Matrix &x, const Matrix &y, int axis = 0);

Matrix read_matrix(BinaryFile &lhs);
Tensor read_tensor(BinaryFile &lhs);

VectorI shape(const Matrix &x);
VectorI shape(const Tensor &x);

VectorI shape(const MatrixI &x);
VectorI shape(const TensorI &x);
VectorI shape(const TensorD &x);

VectorI shape(const vector<Tensor> &x);

Matrix middleCols(const Matrix &X, int start, int stop, int step);
Matrix middleRows(const Matrix &X, int start, int stop, int step);

Vector flatten(const Matrix &x);
Vector one_hot(int i, int size, double value=1);
