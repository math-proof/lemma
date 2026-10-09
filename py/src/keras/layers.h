#pragma once
#include "matrix.h"
#include<vector>
using std::vector;

struct CRF {
	Vector bias;
	Matrix G;
	Matrix kernel;
	Vector left_boundary;
	Vector right_boundary;
	Activation activation;

	CRF(Matrix kernel, Matrix G, Vector bias, Vector left_boundary,
			Vector right_boundary);

	Matrix& viterbi_one_hot(const Matrix &X, Matrix &oneHot);

	VectorI operator ()(const Matrix &X) const;

	VectorI& operator ()(const Matrix &X, VectorI &best_path) const;

	VectorI operator ()(const Matrix &X, const MatrixI &mask_pos) const;

	double loss(const Matrix &X, const VectorI &y) const;
	CRF(BinaryFile &dis);
};

template<Padding padding=Padding::same>
struct Conv1D {

};

template<>
struct Conv1D<Padding::valid> {
	Tensor w;
	Vector bias;
	Activation activate = { Activator::relu };

	Conv1D(BinaryFile &dis, bool bias = true);

	static int initial_offset(int xshape, int yshape, int wshape, int sshape);

//	#stride=(1,1)
	Matrix& operator()(const Matrix &x, Matrix &y, int s = 1) const;
	Matrix operator()(const Matrix &x, int s = 1) const;
};

template<>
struct Conv1D<Padding::same>{
	Tensor w;
	Vector bias;
	Activation activate = { Activator::relu };

	Conv1D(Activation = { Activator::linear });
	Conv1D(BinaryFile &dis);

	void construct(BinaryFile &dis);
//	#stride=(1,1)
	Matrix& operator()(const Matrix &x, Matrix &y) const;
	Matrix operator()(const Matrix &x, int dilation_rate) const;
	Matrix& operator()(const Matrix &x, Matrix &y, int dilation_rate) const;
	Matrix& operator()(const Matrix &x, Matrix &y, bool parallel) const;
	Matrix& operator()(const Matrix &x, Matrix &y, int dilation_rate,
			bool parallel) const;
	Matrix operator()(const Matrix &x) const;
};

template<>
struct Conv1D<Padding::causal>{
	Tensor w;
	Vector bias;
	Activation activate = { Activator::relu };

	Conv1D(BinaryFile &dis);

//	#stride=(1,1)
	Matrix& operator()(const Matrix &x, Matrix &y) const;
	Matrix& operator()(const Matrix &x, Matrix &y, int dilation_rate) const;

	Matrix& operator()(const Matrix &x, Matrix &y, bool parallel) const;
	Matrix& operator()(const Matrix &x, Matrix &y, int dilation_rate,
			bool parallel) const;
	Matrix operator()(const Matrix &x) const;
};

struct DenseLayer {
	/**
	 *
	 */

	Matrix weight;
	Vector bias;
	Activation activation = { Activator::tanh };

	Vector& operator()(const Vector &x, Vector &ret) const;
	Vector& operator()(Vector &x) const;

	Matrix& operator()(const Matrix &x, Matrix &wDense) const;
	Matrix& operator()(Matrix &x) const;
	Tensor& operator()(Tensor &x) const;
	vector<Vector>& operator()(vector<Vector> &x) const;

	DenseLayer();
	DenseLayer(BinaryFile &dis, Activator activator = Activator::tanh);
	void init(BinaryFile &dis);

};

struct Embedding {
	Matrix wEmbedding;

	Matrix& operator()(const VectorI &word, Matrix &wordEmbedding,
			bool parallel) const;

	Matrix& operator()(const VectorI &word, Matrix &wordEmbedding) const;

	Matrix& operator()(const VectorI &word, Matrix &wordEmbedding,
			Matrix &wEmbedding) const;

	Tensor& operator()(const MatrixI &word, Tensor &y) const;
	Tensor operator()(const MatrixI &word) const;
	Matrix operator()(const VectorI &word) const;
	Matrix operator()(const VectorI &word, bool parallel) const;

	void construct(BinaryFile &dis);
	Embedding();
	Embedding(BinaryFile &dis);

	int embed_size();
};

struct RNN {
	using object = ::object<RNN>;

//	Activation recurrent_activation = { Activator::hard_sigmoid };
//	since tensorflow 1.15, recurrent_activation=sigmoid
	Activation recurrent_activation = { Activator::sigmoid };
	Activation activation = { Activator::tanh };

	virtual ~RNN();

	virtual Vector& call(const Matrix &x, Vector &ret) const = 0;

	virtual Vector& call_reverse(const Matrix &x, Vector &ret) const = 0;

	virtual Matrix& call_return_sequences(const Matrix &x,
			Matrix &ret) const = 0;

	virtual Matrix& call_return_sequences_reverse(const Matrix &x,
			Matrix &ret) const = 0;

	virtual TensorD& weight(TensorD &arr);
};

struct Bidirectional {
	RNN::object forward, backward;
	enum merge_mode {
		sum, mul, ave, concat
	};

	merge_mode mode;

	Matrix& operator()(const Tensor &x, Matrix &ret) const;

	Matrix& operator()(const Matrix &x, Matrix &ret) const;

	Vector& operator()(const Matrix &x, Vector &ret) const;
	Vector& operator()(const Matrix &x, Vector &ret, MatrixD &arr) const;
//private:
//	Bidirectional(RNN *forward, RNN *backward, merge_mode mode);
};

/**
 * implimentation of Gated Recurrent Unit
 */

struct BidirectionalGRU: Bidirectional {

	BidirectionalGRU(BinaryFile &dis, merge_mode mode);
};

struct BidirectionalLSTM: Bidirectional {
	BidirectionalLSTM(BinaryFile &dis, merge_mode mode);
};

/**
 * implimentation of Gated Recurrent Unit
 */

struct GRU: RNN {
	Matrix Wxu;
	Matrix Whu;
	Vector bu;

	Matrix Wxr;
	Matrix Whr;
	Vector br;

	Matrix Wxh;
	Matrix Whh;
	Vector bh;

	Vector& call(const Matrix &x, Vector &h) const;
	Vector& call_reverse(const Matrix &x, Vector &h) const;
	Vector& call(const Matrix &x, Vector &h, MatrixD &arr) const;
	Vector& call_reverse(const Matrix &x, Vector &h, MatrixD &arr) const;

	Matrix& call_return_sequences(const Matrix &x, Matrix &ret) const;
	Matrix& call_return_sequences_reverse(const Matrix &x, Matrix &ret) const;

	Vector& activate(const Eigen::Block<const Matrix, 1, -1, 1> &x,
			Vector &h) const;
	Vector& activate(const Eigen::Block<const Matrix, 1, -1, 1> &x, Vector &h,
			MatrixD &arr) const;

	TensorD& weight(TensorD &arr);

	GRU(BinaryFile &dis);
};

struct LSTM: RNN {

	Matrix Wxi;
	Matrix Whi;
	Matrix Wci;
	Vector bi;

	Matrix Wxf;
	Matrix Whf;
	Matrix Wcf;
	Vector bf;

	Matrix Wxc;
	Matrix Whc;
	Vector bc;

	Matrix Wxo;
	Matrix Who;
	Matrix Wco;
	Vector bo;

	LSTM(Matrix Wxi, Matrix Wxf, Matrix Wxc, Matrix Wxo, Matrix Whi, Matrix Whf,
			Matrix Whc, Matrix Who, Vector bi, Vector bf, Vector bc, Vector bo);
	Vector& call(const Matrix &x, Vector &h) const;
	Vector& activate(const Eigen::Block<const Matrix, 1, -1, 1> &x, Vector &h,
			Vector &c) const;

	LSTM(BinaryFile &dis);
	Matrix& call_return_sequences(const Matrix &x, Matrix &arr) const;
	Matrix& call_return_sequences_reverse(const Matrix &x, Matrix &arr) const;
	Vector& call_reverse(const Matrix &x, Vector &h) const;
};

struct Bilinear {
	Bilinear(BinaryFile &dis, Activation activation = { Activator::linear });
	Tensor weight;
	Vector bias;
	Activation activation;
	Tensor operator ()(const Tensor &x, const Tensor &y);
	Vector operator ()(const Vector &x, const Vector &y);
	Matrix operator ()(const Matrix &x, const Matrix &y);
};

struct BilinearMatrixAttention {
	BilinearMatrixAttention(BinaryFile &dis);
	Matrix _weight_matrix;
	double _bias;
	Matrix operator ()(const Matrix &x, const Matrix &y);
};

