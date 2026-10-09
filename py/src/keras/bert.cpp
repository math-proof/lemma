#include "bert.h"
#include "matrix.h"
#include "../std/lagacy.h"
#include "utility.h"

Vector& FeedForward::operator()(const Vector &x, Vector &ret) {
	return ret = x * W1 + b1;
}

vector<Vector> FeedForward::operator()(const vector<Vector> &x) {
	auto y = x * W1;
	if (b1.data())
		y += b1;

	y = activation(y);

	y *= W2;
	if (b2.data())
		y += b2;
	return y;
}

Vector FeedForward::operator()(const Vector &x) {
	Vector y;
	y = x * W1;
	if (b1.data())
		y += b1;

	y = activation(y);

	y *= W2;
	if (b2.data())
		y += b2;
	return y;
}

Tensor FeedForward::operator()(const Tensor &x) {
	auto y = x * W1;
	if (b1.data())
		y += b1;

	y = activation(y);

	y *= W2;
	if (b2.data())
		y += b2;
	return y;
}

Matrix FeedForward::operator()(const Matrix &x) {
	Matrix y;
	y = x * W1;
	if (b1.data())
		add(y, b1);

	y = activation(y);

	y *= W2;
	if (b2.data())
		add(y, b2);
	return y;
}

FeedForward::FeedForward() {

}

FeedForward::FeedForward(BinaryFile &dis, bool use_bias) {
	dis >> W1;
	if (use_bias) {
		dis >> b1;
	}

	dis >> W2;
	if (use_bias) {
		dis >> b2;
	}
}

FeedForward::FeedForward(BinaryFile &dis, Activation activation) {
	dis >> W1;
	dis >> b1;

	dis >> W2;

	dis >> b2;

	this->activation = activation;
}

Tensor& LayerNormalization::operator ()(Tensor &x) {
	auto &deviation = x - mean(x);

	Tensor deviation_copy;
	deviation_copy = deviation;

	auto mean_x = mean(square(deviation_copy));
	return deviation / sqrt(mean_x + epsilon) * gamma + beta;
}

Matrix& LayerNormalization::operator ()(Matrix &x) {
//	print(x);
	x = hadamard_sub(x, mean(x));

	Matrix &deviation = x;

	Matrix deviation_copy;
	deviation_copy = deviation;

	auto mean_square = mean(square(deviation_copy));
	mean_square += epsilon;
	hadamard_div(deviation, sqrt(mean_square));
	mul(deviation, gamma);
	add(deviation, beta);
	return deviation;
}

vector<Vector>& LayerNormalization::operator()(vector<Vector> &x) {
	auto &deviation = x - mean(x);

	vector<Vector> deviation_copy;
	deviation_copy = deviation;

	auto mean_x = mean(square(deviation_copy));
	return deviation / sqrt(mean_x + epsilon) * gamma + beta;
}

Vector& LayerNormalization::operator()(Vector &x) {
	x -= x.mean();
	auto &deviation = x;

	Vector deviation_copy;
	deviation_copy = deviation;
	deviation /= sqrt(square(deviation_copy).mean() + epsilon);
	mul(deviation, gamma);
	deviation += beta;
	return deviation;
}

LayerNormalization::LayerNormalization() {
}

LayerNormalization::LayerNormalization(BinaryFile &dis) {
	construct(dis);
}

void LayerNormalization::construct(BinaryFile &dis) {
	Timer timer(__PRETTY_FUNCTION__);
	dis >> gamma;
	dis >> beta;
}

const double LayerNormalization::epsilon = 1e-12;

VectorI MidIndex::operator()(const MatrixI &input_ids) {
	int batch_size = input_ids.size();
	VectorI res;
	res.resize(batch_size);
	int seq_length = input_ids[0].size();

	for (int k = 0; k < batch_size; ++k) {
		for (int i = 0; i < seq_length; ++i) {
			if (input_ids[k][i] == SEP) {
				res[k] = i + 1;
				break;
			}
		}
	}
	return res;
}

int MidIndex::operator()(const VectorI &input_ids) {
	int seq_length = input_ids.size();

	for (int i = 0; i < seq_length; ++i) {
		if (input_ids[i] == SEP) {
			// i is the index of SEP;
			// i is the number of indices before SEP;
//			then i + 1 will be the number of indices including SEP?
			// return the number of indices including SEP?
			return i + 1;
		}
	}
	return -1;
}

MidIndex::MidIndex(int SEP) {
	this->SEP = SEP;
	Timer timer(__PRETTY_FUNCTION__);

}

int MultiHeadAttention::global_dilation_hyper_parameters(int seq_length, int &lower, int &upper){
	int dilation = ceil(sqrt(seq_length) / 2);
	lower = seq_length / dilation;
	upper = lower;
	return dilation;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence) {

	Matrix Q, K, V;
	Q = K = V = sequence;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence, int h) {

	Matrix Q, K, V;
	Q = K = V = sequence;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V, h);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence, int h,
		bool return_upper_part_only) {

	Matrix Q, K, V;
	K = V = sequence;

	Q = getitem(sequence, { 0, h });

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V, h, true);

	y = reshape_from_batches(y);

	assert(y.size() == 1);

	Matrix res;
	res = y[0];

	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence,
		const Tensor &a_K, const Tensor &a_V, int max_relative_position) {

	Matrix Q, K, V;
	Q = K = V = sequence;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V, a_K, a_V,
			max_relative_position);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence,
		const Tensor &a_K, const Tensor &a_V, int lower, int upper, int dilation) {

	Matrix Q, K, V;
	Q = K = V = sequence;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V, a_K, a_V,
			lower, upper, dilation);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence, const VectorI &indices) {

	Matrix Q = sequence;
	int rows = indices.size();
	Matrix K(rows, sequence.cols());

	for (int i = 0; i < rows; ++i){
		K.row(i) = sequence.row(indices[i]);
	}

	Matrix V = K;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Matrix MultiHeadAttention::operator ()(const Matrix &sequence, const Tensor &a_K,
		const Tensor &a_V, const VectorI &indices) {

	Matrix Q = sequence;
	int rows = indices.size();
	Matrix K(rows, sequence.cols());

	for (int i = 0; i < rows; ++i){
		K.row(i) = sequence.row(indices[i]);
	}

	Matrix V = K;

	Tensor _Q = reshape_to_batches(add(Q *= Wq, bq));
	Tensor _K = reshape_to_batches(add(K *= Wk, bk));
	Tensor _V = reshape_to_batches(add(V *= Wv, bv));

	Tensor &y = scaled_dot_product_attention(_Q, _K, _V, a_K, a_V);

	y = reshape_from_batches(y);
	assert(y.size() == 1);

	Matrix res;
	res = y[0];
	res *= Wo;
	add(res, bo);
	return res;
}

Vector& MultiHeadAttention::operator ()(const Matrix &sequence, Vector &y) {

	Matrix K, V;
	K = V = sequence;

	y = sequence.row(0);
	auto &Q = y;

	vector<Vector> _Q = reshape_to_batches((Q *= Wq) += bq);
	auto _K = reshape_to_batches(add(K *= Wk, bk));
	auto _V = reshape_to_batches(add(V *= Wv, bv));

	vector<Vector> &_y = reshape_from_batches(
			scaled_dot_product_attention(_Q, _K, _V));

	assert(_y.size() == 1);

	y = _y[0];

	y *= Wo;
	y += bo;
	return y;
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(Tensor &Q,
		const Tensor &K, const Tensor &V) {
	auto &e = batch_dot<true>(Q, K);

	e /= sqrt(K[0].cols());

	auto &a = softmax(e);
	return batch_dot(a, V);
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(Tensor &Q,
		const Tensor &K, const Tensor &V, int h) {

	int seq_length = Q[0].rows();
	int embed_size = K[0].cols();
	double sqrt_dz = sqrt(embed_size);

//	Matrix ksi;
//	ksi.resize(seq_length, seq_length);
//	ksi << Matrix::Zero(h, h), Matrix::Ones(h, seq_length - h), Matrix::Ones(
//			seq_length - h, h), Matrix::Zero(seq_length - h, seq_length - h);
//
//	ksi += Matrix::Identity(seq_length, seq_length);
//	ksi = 1 - ksi;
//	ksi *= 100000;
//
//	auto &a = batch_dot<true>(Q, K);
//
//	a /= sqrt(embed_size);
//
//	a -= ksi;
//
//	auto &s = softmax(a);
//	return batch_dot(s, V);

	int batch_size = Q.size();
	Tensor &z = Q;
	for (int k = 0; k < batch_size; ++k) {
		auto &Qk = Q[k];
		auto &Kk = K[k];
		auto &Vk = V[k];

		Matrix W0 = Qk.topRows(h) * Kk.bottomRows(seq_length - h).transpose();
		W0 /= sqrt_dz;
		W0 = exp(W0);

		Matrix W1 = Qk.bottomRows(seq_length - h) * Kk.topRows(h).transpose();
		W1 /= sqrt_dz;
		W1 = exp(W1);

		Vector Dk = Qk.cwiseProduct(Kk).rowwise().sum();
		Dk /= sqrt_dz;
		Dk = exp(Dk);

		Vector D0 = Dk.leftCols(h), D1 = Dk.rightCols(seq_length - h);
		Matrix V0 = Vk.topRows(h), V1 = Vk.bottomRows(seq_length - h);

		Vector den0 = W0.rowwise().sum();
		den0 += D0;

		Vector den1 = W1.rowwise().sum();
		den1 += D1;

		Matrix num0 = W0 * V1;
		Matrix num1 = W1 * V0;

		num0 += hadamard_mul(V0, D0);
		num1 += hadamard_mul(V1, D1);

//		z[k].resize(seq_length, embed_size);
		z[k] << hadamard_div(num0, den0), hadamard_div(num1, den1);
	}

	return z;
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(Tensor &Q,
		const Tensor &K, const Tensor &V, int h, bool return_upper_part_only) {
	int batch_size = K.size();
	int seq_length = K[0].rows();
	int embed_size = K[0].cols();

	double sqrt_dz = sqrt(embed_size);

	Tensor &z = Q;

	for (int k = 0; k < batch_size; ++k) {
		auto &Qk = Q[k];
		auto &Kk = K[k];
		auto &Vk = V[k];

		Matrix W0 = Qk * Kk.bottomRows(seq_length - h).transpose();
		W0 /= sqrt_dz;
		W0 = exp(W0);

		Vector D0 = Qk.cwiseProduct(Kk.topRows(h)).rowwise().sum();

		D0 /= sqrt_dz;
		D0 = exp(D0);

		Matrix V0 = Vk.topRows(h), V1 = Vk.bottomRows(seq_length - h);

		Vector den0 = W0.rowwise().sum();
		den0 += D0;

		Matrix num0 = W0 * V1;
		num0 += hadamard_mul(V0, D0);

		z[k] = hadamard_div(num0, den0);
	}

	return z;
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(const Tensor &Q,
		const Tensor &K, Tensor &V, const Tensor &a_K, const Tensor &a_V,
		int k_max) {
//	print(k_max);
	int batch_size = Q.size();
	int embed_size = Q[0].cols();
	int seq_length = a_K.size();

	auto &z = V;
	double sqrt_dk = sqrt(embed_size);

	Matrix tensorArray(seq_length, embed_size);

	for (int k = 0; k < batch_size; ++k) {
		auto &Qk = Q[k];
		auto Kk = K[k].transpose();
		auto &Vk = V[k];
		auto &zk = z[k];

		for (int i = 0; i < seq_length; ++i) {
			int start;
			int size = PositionEmbedding::slice(seq_length, i, k_max, start);

			Vector aki = Qk.row(i) * (Kk.middleCols(start, size) + a_K[i])
					/ sqrt_dk;
			// output is of shape (embed_size,)
			tensorArray.row(i) = softmax(aki) * (Vk.middleRows(start, size) + a_V[i]);
		}

		zk = tensorArray;
	}

	return z;
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(const Tensor &Q,
		const Tensor &K, Tensor &V, const Tensor &a_K, const Tensor &a_V,
		int lower, int upper, int dilation) {
//	Timer timer(__PRETTY_FUNCTION__);

	int batch_size = Q.size();
	int embed_size = Q[0].cols();
	int seq_length = a_K.size();

	auto &z = V;
	double sqrt_dk = sqrt(embed_size);

	Matrix tensorArray(seq_length, embed_size);

	for (int k = 0; k < batch_size; ++k) {
		auto &Qk = Q[k];
		auto Kk = K[k].transpose();
		auto &Vk = V[k];
		auto &zk = z[k];

		for (int i = 0; i < seq_length; ++i) {
			int beta_i;
			int zeta_i = PositionEmbedding::slice(seq_length, i, lower, upper, dilation, beta_i);

//			print("beta_i =", beta_i);
//			print("zeta_i =", zeta_i);
//			if (shape(middleCols(Kk, beta_i, zeta_i, dilation)) != shape(a_K[i])){
//
//				if (dilation > 1){
//					print("i =", i);
//					print("beta_i =", beta_i);
//					print("zeta_i =", zeta_i);
//					print("gram_width =", ceiling(zeta_i - beta_i, dilation));
//				}
//
//				print("error detected: shapes dismatch!");
//				print("middleCols(Kk, beta_i, zeta_i, dilation).shape =", shape(middleCols(Kk, beta_i, zeta_i, dilation)));
//				print("a_K[i].shape =", shape(a_K[i]));
//				throw;
//			}
//
//			if (shape(middleRows(Vk, beta_i, zeta_i, dilation)) != shape(a_V[i])){
//				print("error detected: shapes dismatch!");
//				print("middleRows(Vk, beta_i, zeta_i, dilation).shape =", shape(middleRows(Vk, beta_i, zeta_i, dilation)));
//				print("a_V[i].shape =", shape(a_V[i]));
//				throw;
//			}

			Vector aki = Qk.row(i) * (middleCols(Kk, beta_i, zeta_i, dilation) + a_K[i])
					/ sqrt_dk;
			// output is of shape (embed_size,)
			tensorArray.row(i) = softmax(aki) * (middleRows(Vk, beta_i, zeta_i, dilation) + a_V[i]);
		}

		zk = tensorArray;
	}

	return z;
}

Tensor& MultiHeadAttention::scaled_dot_product_attention(const Tensor &Q,
		const Tensor &K, Tensor &V, const Tensor &a_K, const Tensor &a_V) {
	int batch_size = Q.size();
	int embed_size = Q[0].cols();
	int seq_length = a_K.size();

	auto &z = V;
	double sqrt_dk = sqrt(embed_size);

	Matrix tensorArray(seq_length, embed_size);

	for (int k = 0; k < batch_size; ++k) {
		auto &Qk = Q[k];
		auto Kk = K[k].transpose();
		auto &Vk = V[k];
		auto &zk = z[k];

		for (int i = 0; i < seq_length; ++i) {
			Vector aki = Qk.row(i) * (Kk + a_K[i]) / sqrt_dk;
			// output is of shape (embed_size,)
			tensorArray.row(i) = softmax(aki) * (Vk + a_V[i]);
		}

		zk = tensorArray;
	}

	return z;
}

vector<Vector>& MultiHeadAttention::scaled_dot_product_attention(
		vector<Vector> &Q, const Tensor &K, const Tensor &V) {
	vector<Vector> &e = batch_dot<true>(Q, K);

	e /= sqrt(K[0].cols());

	return batch_dot(softmax(e), V);
}

Tensor& MultiHeadAttention::reshape_to_batches(Tensor &x) {
	int batch_size = x.size();
	int hidden_size = x[0].cols();

	int size_per_head = hidden_size / num_attention_heads;

	x.resize(batch_size * num_attention_heads);
	for (int i = batch_size - 1; i >= 0; --i) {
		for (int j = 0; j < num_attention_heads; ++j)
			x[i * num_attention_heads + j] = x[i].middleCols(j * size_per_head,
					size_per_head);
	}

	return x;
}

Tensor MultiHeadAttention::reshape_to_batches(Matrix &x) {
	Tensor _x(num_attention_heads);
//	_x[0] = x;

	int hidden_size = x.cols();

	int size_per_head = hidden_size / num_attention_heads;

	for (int j = 0; j < num_attention_heads; ++j)
		_x[j] = x.middleCols(j * size_per_head, size_per_head);

	return _x;
}

vector<Vector>& MultiHeadAttention::reshape_to_batches(vector<Vector> &x) {
	int batch_size = x.size();
	int hidden_size = x[0].cols();

	int size_per_head = hidden_size / num_attention_heads;

	x.resize(batch_size * num_attention_heads);
	for (int i = batch_size - 1; i >= 0; --i) {
		for (int j = 0; j < num_attention_heads; ++j)
			x[i * num_attention_heads + j] = x[i].middleCols(j * size_per_head,
					size_per_head);
	}

	return x;
}

vector<Vector> MultiHeadAttention::reshape_to_batches(Vector &x) {
	vector<Vector> _x(num_attention_heads);
//	_x[0] = x;

	int hidden_size = x.cols();
	int size_per_head = hidden_size / num_attention_heads;

	for (int j = 0; j < num_attention_heads; ++j)
		_x[j] = x.middleCols(j * size_per_head, size_per_head);

	return _x;
}

Tensor& MultiHeadAttention::reshape_from_batches(Tensor &x) {
// transforming tensor x from shape
//	(batch_size * num_attention_heads, seq_length, embed_size / num_attention_heads);
//	to shape
//	(batch_size, seq_length, embed_size);

	int batch_size = x.size() / num_attention_heads;
	int size_per_head = x[0].cols();
	int embed_size = size_per_head * num_attention_heads;
	int seq_length = x[0].rows();

	for (int k = 0; k < batch_size; ++k) {
		Matrix res = Matrix::Zero(seq_length, embed_size);
		for (int j = 0; j < num_attention_heads; ++j)
			res.middleCols(j * size_per_head, size_per_head) = x[k
					* num_attention_heads + j];
		x[k] = res;
	}

	x.resize(batch_size);
	return x;
}

MultiHeadAttention::MultiHeadAttention() { // @suppress("Class members should be properly initialized")
}

vector<Vector>& MultiHeadAttention::reshape_from_batches(vector<Vector> &x) {
	int batch_size = x.size() / num_attention_heads;
	int size_per_head = x[0].cols();
	int hidden_size = size_per_head * num_attention_heads;

	for (int k = 0; k < batch_size; ++k) {
		Matrix res = Vector::Zero(hidden_size);
		for (int j = 0; j < num_attention_heads; ++j)
			res.middleCols(j * size_per_head, size_per_head) = x[k
					* num_attention_heads + j];
		x[k] = res;
	}

	x.resize(batch_size);
	return x;

}

MultiHeadAttention::MultiHeadAttention(BinaryFile &dis,
		int num_attention_heads) :
		num_attention_heads(num_attention_heads) {
	Timer timer(__PRETTY_FUNCTION__);

	dis >> Wq;
	dis >> bq;

	dis >> Wk;
	dis >> bk;

	dis >> Wv;
	dis >> bv;

	dis >> Wo;
	dis >> bo;
}

Tensor& PositionEmbedding::operator ()(Tensor &sequence, const VectorI &mid) {
	int batch_size = sequence.size();
	int seq_length = sequence[0].rows();

	for (int k = 0; k < batch_size; ++k) {
		Matrix former = embeddings.topRows(mid[k]);
		Matrix latter = embeddings.middleRows(1, seq_length - mid[k]);
		Matrix pos_embeddings;
		pos_embeddings << former, latter;
		sequence[k] += pos_embeddings;
	}

	return sequence;
}

//http://localhost/sympy/axiom.php?module=geometry/piece/to/sin/exp
Matrix PositionEmbedding::sinusoidal_embedding(int startRow, int n,
		int embedding_dim) {
	Matrix embeddings(n, embedding_dim);
	double emb_common = -log(10000) / (embedding_dim / 2 - 1);
	int endRow = startRow + n;
	double pi_half = PI / 2;

	for (int i = startRow; i < endRow; ++i) {
		for (int j = 0; j < embedding_dim; ++j) {
			embeddings(i - startRow, j) = sin(exp((j / 2) * emb_common) * i + pi_half * (j % 2));
		}
	}

	return embeddings;
}

Matrix PositionEmbedding::topRows(int n, int embedding_dim) {
	if (embeddings.data()) {
		return embeddings.topRows(n);
	} else {
		return sinusoidal_embedding(0, n, embedding_dim);
	}
}

Matrix PositionEmbedding::middleRows(int startRow, int n, int embedding_dim) {
	if (embeddings.data()) {
		return embeddings.middleRows(startRow, n);
	} else {
		return sinusoidal_embedding(startRow, n, embedding_dim);
	}
}

Matrix& PositionEmbedding::operator ()(Matrix &sequence, int mid) {
	int seq_length = sequence.rows();
	int embed_size = sequence.cols();
	Matrix former = topRows(mid, embed_size);
	Matrix latter = middleRows(1, seq_length - mid, embed_size);

	Matrix pos_embeddings(seq_length, embed_size);
	pos_embeddings << former, latter;
	sequence += pos_embeddings;

	return sequence;
}

Matrix& PositionEmbedding::operator ()(Matrix &sequence) {
	int seq_length = sequence.rows();
	sequence += embeddings.topRows(seq_length);
	return sequence;
}

int PositionEmbedding::max_relative_position() {
	return this->embeddings.rows() / 2;
}

//# https://github.com/tensorflow/tensor2tensor/blob/9e0a894034d8090892c238df1bd9bd3180c2b9a3/tensor2tensor/layers/common_attention.py#L1556-L1587
//# Shift values to be >= 0. Each integer still uniquely identifies a relative
//# position difference.
Tensor PositionEmbedding::operator ()(int seq_length) {
	int k = max_relative_position();

	MatrixI indices = int_zeros(seq_length, seq_length);

	for (int i = 0; i < seq_length; ++i) {
		for (int j = 0; j < seq_length; ++j) {
			indices[i][j] = k + clip(j - i, -k, k);
		}
	}

	return gather(embeddings, indices);
}

//http://localhost/sympy/axiom.php?module=keras.matmul_softmax.to.lamda.matmul.softmax.clip.bert.position_representation.relative.band_part_mask
int PositionEmbedding::slice(int seq_length, int i, int k_max, int &start) {
	start = i - k_max;
	int stop = i + k_max + 1;
	start = relu(start);
	stop = std::min(seq_length, stop);
	return stop - start;
}

int PositionEmbedding::slice(int seq_length, int i, int lower, int upper, int dilation, int &beta) {
	beta = i - lower;
	beta = std::max(beta, mod(beta, dilation));
	int zeta = i + upper + 1;
	zeta = std::min(seq_length, zeta);
	return zeta;
}

int PositionEmbedding::translate_j(int i, int j, int n, int lower) {
	return std::min(n - 1, i + j - std::min(i, lower));
}

Tensor PositionEmbedding::operator ()(int seq_length, int k_max) {
	int k = max_relative_position();
	MatrixI indices(seq_length);

	for (int i = 0; i < seq_length; ++i) {
		int start;
		int size = slice(seq_length, i, k_max, start);

		indices[i].resize(size);
		for (int j = 0; j < size; ++j) {
			indices[i][j] = k + clip(j - std::min(i, k_max), -k, k);
		}
	}
//beware that indices is not a rectangular matrix!
	return gather(embeddings, indices);
}

Tensor PositionEmbedding::operator ()(const VectorI &r, int k_max) {
	int seq_length = r.size();
	int k = max_relative_position();

	MatrixI indices(seq_length);

	for (int i = 0; i < seq_length; ++i) {
		int beta_i;
		int gram_width = slice(seq_length, i, k_max, beta_i);
		indices[i].resize(gram_width);
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = k + clip(r[j + beta_i] - r[i], -k, k);
		}
	}
//beware that indices is not a rectangular matrix!
	return gather(embeddings, indices);
}

Tensor PositionEmbedding::operator ()(const VectorI &r, int lower, int upper, int dilation) {
	int seq_length = r.size();
	int k = max_relative_position();

	MatrixI indices(seq_length);

	for (int i = 0; i < seq_length; ++i) {
		int beta_i;
		int zeta_i = slice(seq_length, i, lower, upper, dilation, beta_i);
		int gram_width = ceiling(zeta_i - beta_i, dilation);
		indices[i].resize(gram_width);
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = k + clip(r[dilation * j + beta_i] - r[i], -k, k);
		}
	}
//beware that indices is not a rectangular matrix!
	return gather(embeddings, indices);
}

Tensor PositionEmbedding::operator ()(const VectorI &r, const VectorI &d) {
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = r.size();
	int k = max_relative_position();

	int m = d.size();
	MatrixI indices = int_zeros(seq_length, m);

	for (int i = 0; i < seq_length; ++i) {
		for (int j = 0; j < m; ++j) {
			indices[i][j] = k + clip(r[d[j]] - r[i], -k, k);
		}
	}

	return gather(embeddings, indices);
}

// the result is sure to be a rectangular tensor!
Tensor PositionEmbedding::operator ()(const VectorI &r, int k_max, bool debug) {
	int seq_length = r.size();
	int k = max_relative_position();

	int gram_width = std::min(seq_length, k_max * 2 + 1);
	MatrixI indices = int_zeros(seq_length, gram_width);

	for (int i = 0; i < seq_length; ++i) {
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = k + clip(r[translate_j(i, j, seq_length, k_max)] - r[i], -k, k);
		}
	}
	return gather(embeddings, indices);
}

MatrixI PositionEmbedding::get_relative_indices(const VectorI &r, int k_max) {
//	int seq_length = r.size();
	int n = r.size();
	int gram_width = std::min(n, k_max * 2 + 1);
	MatrixI indices = int_zeros(n, gram_width);

	for (int i = 0; i < n; ++i) {
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = r[translate_j(i, j, n, k_max)] - r[i];
		}
	}
	return indices;
}

MatrixI PositionEmbedding::get_relative_indices(const VectorI &r, int lower, int upper) {
//	int seq_length = r.size();
	int n = r.size();
	int gram_width = std::min(n, lower + upper + 1);
	MatrixI indices = int_zeros(n, gram_width);

	for (int i = 0; i < n; ++i) {
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = r[translate_j(i, j, n, lower)] - r[i];
		}
	}
	return indices;
}

int PositionEmbedding::get_relative_indices(const VectorI &r, int lower, int upper, int i, int j) {
	int n = r.size();
	int gram_width = std::min(n, lower + upper + 1);
	MatrixI indices = int_zeros(n, gram_width);

	int beta_i = relu(i - lower);
	j -= beta_i;
	return r[translate_j(i, j, n, lower)] - r[i];
}

MatrixI PositionEmbedding::get_absolute_indices(const VectorI &r, int k_max) {
	int n = r.size();
	int k = max_relative_position();

	int gram_width = std::min(n, k_max * 2 + 1);
	MatrixI indices = int_zeros(n, gram_width);

	for (int i = 0; i < n; ++i) {
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = k + clip(r[translate_j(i, j, n, k_max)] - r[i], -k, k);
		}
	}
	return indices;
}

MatrixI PositionEmbedding::get_absolute_indices(const VectorI &r, int lower, int upper) {
	int n = r.size();
	int k = max_relative_position();

	int gram_width = std::min(n, lower + upper + 1);
	MatrixI indices = int_zeros(n, gram_width);

	for (int i = 0; i < n; ++i) {
		for (int j = 0; j < gram_width; ++j) {
			indices[i][j] = k + clip(r[translate_j(i, j, n, lower)] - r[i], -k, k);
		}
	}
	return indices;
}

Tensor& PositionEmbedding::operator ()(Tensor &sequence) {
	int batch_size = sequence.size();
	int seq_length = sequence[0].rows();

	Matrix pos_embeddings = embeddings.topRows(seq_length);

	for (int k = 0; k < batch_size; ++k) {
		sequence[k] += pos_embeddings;
	}

	return sequence;
}

PositionEmbedding::PositionEmbedding(BinaryFile &dis) {
	construct(dis);
}

void PositionEmbedding::construct(BinaryFile &dis) {
	Timer timer(__PRETTY_FUNCTION__);
	dis >> embeddings;
}

PositionEmbedding::PositionEmbedding() {
	Timer timer(__PRETTY_FUNCTION__);
}

MatrixI SegmentInput::operator ()(const MatrixI &inputToken,
		VectorI &inputMid) {
	int batch_size = inputToken.size();
	int length = inputToken[0].size();
	MatrixI inputSegment(batch_size);

	for (int k = 0; k < batch_size; ++k) {
		inputSegment[k].resize(length);
		int mid = inputMid[k];
		stosd(&inputSegment[k][0], 0, mid);
		stosd(&inputSegment[k][mid], 1, length - mid);
	}
	return inputSegment;
}

VectorI SegmentInput::operator ()(const VectorI &inputToken, int mid) {
	int length = inputToken.size();
//	cout << "inputToken.size() = " << inputToken.size() << endl;
	VectorI inputSegment(length);

//	cout << "inputSegment.size() = " << inputSegment.size() << endl;

//	cout << "inputSegment(0) = " << inputSegment(0) << endl;

//	cout << "inputSegment(mid) = " << inputSegment(mid) << endl;

	stosd(&inputSegment[0], 0, mid);

	stosd(&inputSegment[mid], 1, length - mid);

	return inputSegment;
}

BertEmbedding::BertEmbedding(BinaryFile &dis) :
		wordEmbedding(dis),

		segmentEmbedding(dis),

		positionEmbedding(dis),

		layerNormalization(dis),

		embeddingMapping(dis, Activator::linear) {
	Timer timer(__PRETTY_FUNCTION__);
}

BertEmbedding::BertEmbedding(BinaryFile &dis,
		bool sinusoidal_positional_embedding) :
		wordEmbedding(dis),

		segmentEmbedding(dis),

		layerNormalization(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

Matrix BertEmbedding::operator ()(VectorI &input_ids, int inputMid,
		const VectorI &inputSegment) {
	auto embeddings = wordEmbedding(input_ids);

	Matrix segment_layer;
	segmentEmbedding(inputSegment, segment_layer);
//	cout << "segment_layer = " << segment_layer << endl;

	embeddings += segment_layer;
//	cout << "embeddings = " << embeddings << endl;
	auto &embed_layer = positionEmbedding(embeddings, inputMid);
	embed_layer = layerNormalization(embed_layer);

	if (hidden_size() != embed_dim()) {
		embeddings = embeddingMapping(embeddings);
	}

	return embeddings;
}

Tensor BertEmbedding::operator ()(VectorI &input_ids, int inputMid,
		const VectorI &inputSegment, bool) {
	Tensor tensor;
	auto embeddings = wordEmbedding(input_ids);
	auto word_embeddings = embeddings;
	tensor.push_back(word_embeddings);

	Matrix segment_layer;
	segmentEmbedding(inputSegment, segment_layer);

	embeddings += segment_layer;
	auto segment_embeddings = embeddings;
	tensor.push_back(segment_embeddings);

	auto &embed_layer = positionEmbedding(embeddings, inputMid);
	auto position_embeddings = embed_layer;
	tensor.push_back(position_embeddings);

	embed_layer = layerNormalization(embed_layer);
	tensor.push_back(embed_layer);

	if (hidden_size() != embed_dim()) {
		embeddings = embeddingMapping(embeddings);
	}

	return tensor;
}

int BertEmbedding::embed_dim() {
	return wordEmbedding.wEmbedding.cols();
}

int BertEmbedding::hidden_size() {
	if (embeddingMapping.weight.data())
		return embeddingMapping.weight.cols();
	return embed_dim();
}

Matrix BertEmbedding::operator ()(const VectorI &input_ids,
		const VectorI &inputSegment) {
	auto embeddings = wordEmbedding(input_ids);

	Matrix segment_layer;
	segmentEmbedding(inputSegment, segment_layer);
//	cout << "segment_layer = " << segment_layer << endl;

	embeddings += segment_layer;
//	cout << "embeddings = " << embeddings << endl;
	auto &embed_layer = positionEmbedding(embeddings);
	embed_layer = layerNormalization(embed_layer);

	if (hidden_size() != embed_dim()) {
		embeddings = embeddingMapping(embeddings);
	}

	return embeddings;
}

Matrix BertEmbedding::operator ()(const VectorI &input_ids) {
	return (*this)(input_ids, VectorI(input_ids.size()));
}

SelfAttentionEncoder::SelfAttentionEncoder(BinaryFile &dis, int num_attention_heads,
		Activation hidden_act) :
		MultiHeadAttention(dis, num_attention_heads), MultiHeadAttentionNorm(
				dis), FeedForward(dis, hidden_act), FeedForwardNorm(dis) {
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer) {
	input_layer += MultiHeadAttention(input_layer);
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, int h) {
	input_layer += MultiHeadAttention(input_layer, h);
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, int h,
		bool return_upper_part_only) {
	auto input_sliced = getitem(input_layer, range(h));
	input_layer = MultiHeadAttention(input_layer, h, return_upper_part_only);

	input_layer += input_sliced;
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, const Tensor &a_K,
		const Tensor &a_V, int max_relative_position) {
	input_layer += MultiHeadAttention(input_layer, a_K, a_V,
			max_relative_position);
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, const Tensor &a_K,
		const Tensor &a_V, int lower, int upper, int dilation) {
	input_layer += MultiHeadAttention(input_layer, a_K, a_V,
			lower, upper, dilation);
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, const VectorI &indices) {
	input_layer += MultiHeadAttention(input_layer, indices);
	return MultiHeadAttentionNorm(input_layer);
}

Matrix& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, const VectorI &indices) {
	input_layer += MultiHeadAttention(input_layer, a_K, a_V, indices);
	return MultiHeadAttentionNorm(input_layer);
}

Vector& SelfAttentionEncoder::wrap_attention(Matrix &input_layer, Vector &y) {
	y = MultiHeadAttention(input_layer, y);
	y += input_layer.row(0);
	return MultiHeadAttentionNorm(y);
}

Tensor& SelfAttentionEncoder::wrap_feedforward(Tensor &input_layer) {
	return FeedForwardNorm(input_layer + FeedForward(input_layer));
}

Matrix& SelfAttentionEncoder::wrap_feedforward(Matrix &input_layer) {
	input_layer += FeedForward(input_layer);
	return FeedForwardNorm(input_layer);
}

vector<Vector>& SelfAttentionEncoder::wrap_feedforward(vector<Vector> &input_layer) {
	return FeedForwardNorm(input_layer + FeedForward(input_layer));
}

Vector& SelfAttentionEncoder::wrap_feedforward(Vector &input_layer) {
	input_layer += FeedForward(input_layer);
	return FeedForwardNorm(input_layer);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer) {
	auto &inputs = wrap_attention(input_layer);
	return wrap_feedforward(inputs);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, int h) {
	auto &inputs = wrap_attention(input_layer, h);
	return wrap_feedforward(inputs);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, int h,
		bool return_upper_part_only) {
	auto &inputs = wrap_attention(input_layer, h, return_upper_part_only);
	auto &y = wrap_feedforward(inputs);
	return y;
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, const Tensor &a_K,
		const Tensor &a_V, int max_relative_position) {
	auto &inputs = wrap_attention(input_layer, a_K, a_V, max_relative_position);
	return wrap_feedforward(inputs);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, const Tensor &a_K,
		const Tensor &a_V, int lower, int upper, int dilation) {
	auto &inputs = wrap_attention(input_layer, a_K, a_V, lower, upper, dilation);
	return wrap_feedforward(inputs);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, const VectorI &indices) {
	auto &inputs = wrap_attention(input_layer, indices);
	return wrap_feedforward(inputs);
}

Matrix& SelfAttentionEncoder::operator ()(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, const VectorI &indices) {
	auto &inputs = wrap_attention(input_layer, a_K, a_V, indices);
	return wrap_feedforward(inputs);
}

SelfAttentionEncoder::SelfAttentionEncoder() {
}

Vector& SelfAttentionEncoder::operator ()(Matrix &input_layer, Vector &y) {
	auto &inputs = wrap_attention(input_layer, y);
	return wrap_feedforward(inputs);
}

AlbertTransformer::AlbertTransformer(BinaryFile &dis, int num_hidden_layers,
		int num_attention_heads, Activation hidden_act) :
		num_hidden_layers(num_hidden_layers), encoder(dis, num_attention_heads,
				hidden_act) {
	Timer timer(__PRETTY_FUNCTION__);
}

BertTransformer::BertTransformer(BinaryFile &dis, int num_hidden_layers,
		int num_attention_heads, Activation hidden_act) :
		encoder(num_hidden_layers) {
	Timer timer(__PRETTY_FUNCTION__);

	for (int i = 0; i < num_hidden_layers; ++i) {
		encoder[i] = SelfAttentionEncoder(dis, num_attention_heads, hidden_act);
	}
}

SelfAttentionEncoder& BertTransformer::operator [](int i) {
	return encoder[i];
}

Vector& AlbertTransformer::operator ()(Matrix &input_layer, Vector &y) {
	auto &last_layer = input_layer;
	for (int i = 0; i < num_hidden_layers; ++i) {
//		print(last_layer);
		if (i == num_hidden_layers - 1) {
			y = encoder(last_layer, y);
		} else
			last_layer = encoder(last_layer);
	}
	return y;
}

Matrix& AlbertTransformer::operator ()(Matrix &y) {
	for (int i = 0; i < num_hidden_layers; ++i) {
		y = encoder(y);
	}
	return y;
}

Matrix& AlbertTransformer::operator ()(Matrix &y, int h) {
	for (int i = 0; i < num_hidden_layers; ++i) {
		y = encoder(y, h);
	}
	return y;
}

Matrix& AlbertTransformer::operator ()(Matrix &y, int cross_attention_height,
		bool return_upper_part_only) {
	for (int i = 0; i < num_hidden_layers - 1; ++i) {
		y = encoder(y, cross_attention_height);
	}

	y = encoder(y, cross_attention_height, return_upper_part_only);
	return y;
}

Matrix& AlbertTransformer::operator ()(Matrix &y, const Tensor &a_K,
		const Tensor &a_V, int k_max) {
	auto a_K_T = transpose<0, 2, 1>(a_K);
	for (int i = 0; i < num_hidden_layers; ++i) {
		y = encoder(y, a_K_T, a_V, k_max);
	}
	return y;
}

Matrix& BertTransformer::operator ()(Matrix &y, const vector<Tensor> &a_V, const VectorI &indices) {
	int num_hidden_layers = this->num_hidden_layers();
	vector<Tensor> a_K_T(num_hidden_layers);
	for (int i = 0; i < num_hidden_layers; ++i){
		a_K_T[i] = transpose<0, 2, 1>(a_V[i]);
	}

	for (int i = 0; i < num_hidden_layers; ++i) {
		y = encoder[i](y, a_K_T[i], a_V[i], indices);
	}
	return y;
}

Matrix& BertTransformer::operator ()(Matrix &y, const Tensor &a_K,
		const Tensor &a_V, int k_max) {
	auto a_K_T = transpose<0, 2, 1>(a_K);
	int num_hidden_layers = this->num_hidden_layers();
	for (int i = 0; i < num_hidden_layers; ++i) {
		y = encoder[i](y, a_K_T, a_V, k_max);
	}
	return y;
}

Matrix& BertTransformer::operator ()(Matrix &y, const vector<Tensor> &a_V,
		int lower, int upper, const VectorI &dilations) {
//	Timer timer(__PRETTY_FUNCTION__);
	int num_hidden_layers = this->num_hidden_layers();
	vector<Tensor> a_K_T(num_hidden_layers);
	for (int i = 0; i < num_hidden_layers; ++i){
		a_K_T[i] = transpose<0, 2, 1>(a_V[i]);
	}

	for (int i = 0; i < num_hidden_layers; ++i) {
		int dilation = dilations[i];
		y = encoder[i](y, a_K_T[i], a_V[i], lower * dilation, upper * dilation, dilation);
	}
	return y;
}

int BertTransformer::num_hidden_layers(){
	return encoder.size();
}

Vector& BertTransformer::operator ()(Matrix &input_layer, Vector &y) {
	auto &last_layer = input_layer;
	int num_hidden_layers = this->num_hidden_layers();
	for (int i = 0; i < num_hidden_layers; ++i) {
		if (i == num_hidden_layers - 1) {
			y = (*this)[i](last_layer, y);
		} else
			last_layer = (*this)[i](last_layer);
	}
	return y;
}

//bool cross_layer_parameter_sharing = true;
Pairwise::Pairwise(BinaryFile &dis, const string &vocab,
		int num_attention_heads, bool symmetric_position_embedding,
		int num_hidden_layers) :
		tokenizer(vocab),

		symmetric_position_embedding(symmetric_position_embedding),

		midIndex(tokenizer.vocab.at(u"[SEP]")),

		bertEmbedding(dis),

		transformer(dis, num_hidden_layers, num_attention_heads, {Activator::gelu}),

		poolerDense(dis),

		similarityDense(dis, Activator::sigmoid) {
	Timer timer(__PRETTY_FUNCTION__);
}

//bool cross_layer_parameter_sharing = true;
PretrainingAlbert::PretrainingAlbert(BinaryFile &dis, Activation hidden_act,
		int num_attention_heads, int num_hidden_layers) :
		bertEmbedding(dis),

		transformer(dis, num_hidden_layers, num_attention_heads, hidden_act) {
	Timer timer(__PRETTY_FUNCTION__);

}

PretrainingAlbertChinese::PretrainingAlbertChinese(BinaryFile &dis,
		int num_attention_heads, int num_hidden_layers) :
		PretrainingAlbert(dis, { Activator::relu }, num_attention_heads,
				num_hidden_layers) {
	Timer timer(__PRETTY_FUNCTION__);

}

PretrainingAlbertEnglish::PretrainingAlbertEnglish(BinaryFile &dis,
		int num_hidden_layers) :
		PretrainingAlbert(dis, { Activator::gelu },
		/*num_attention_heads = 12*/12, num_hidden_layers) {
	Timer timer(__PRETTY_FUNCTION__);

}

#include "../json/json.h"
Json::Value readFromStream(const string &json_file);

double Pairwise::operator ()(VectorI &input_ids) {
	auto inputMid = midIndex(input_ids);
	auto inputSegment = segmentInput(input_ids, inputMid);

	auto embed_layer =
			symmetric_position_embedding ?
					bertEmbedding(input_ids, inputMid, inputSegment) :
					bertEmbedding(input_ids, inputSegment);

	Vector clsEmbedding;
	transformer(embed_layer, clsEmbedding);

	auto &sent = poolerDense(clsEmbedding);

	sent = similarityDense(sent);

	return sent(0);
}

Vector PretrainingAlbert::operator ()(const VectorI &input_ids) {
//	print(input_ids);

	auto embed_layer = bertEmbedding(input_ids);

//	print(embed_layer);

	Vector clsEmbedding;
	transformer(embed_layer, clsEmbedding);

	return clsEmbedding;
}

double Pairwise::operator ()(const vector<String> &s) {
	auto v = tokenizer.convert_tokens_to_ids(s);
	return (*this)(v);
}

double Pairwise::operator ()(String &x, String &y) {
	if (x.size() > 510) {
		x.resize(510);
	}

	if (y.size() > 510) {
		y.resize(510);
	}

//	cout << "x = " << x << endl;
//	cout << "y = " << y << endl;
	return (*this)(tokenizer.tokenize(x, y));
}

vector<String> PretrainingAlbertChinese::tokenize(const String &text) {
	vector<String> s_x;
	s_x.push_back(u"[CLS]");
	s_x << FullTokenizer::instance_cn().tokenize(text);
	s_x.push_back(u"[SEP]");
	return s_x;
}

//#include "sentencepiece.h"

vector<String> PretrainingAlbertEnglish::tokenize(const String &text) {
	vector<String> s_x;
	s_x.push_back(u"[CLS]");
	s_x << FullTokenizer::instance_en().tokenize(text);
	s_x.push_back(u"[SEP]");
	return s_x;
}

Vector PretrainingAlbertChinese::operator ()(const String &str) {
	return (*this)(
			FullTokenizer::instance_cn().convert_tokens_to_ids(tokenize(str)));
}

Vector PretrainingAlbertEnglish::operator ()(const String &str) {
	return (*this)(
			FullTokenizer::instance_en().convert_tokens_to_ids(tokenize(str)));
}

double Pairwise::operator ()(const char16_t *_x, const char16_t *_y) {
	String x = _x;
	String y = _y;
	cout << "first sentence: " << x << endl;
	cout << "second sentence: " << y << endl;
	return (*this)(x, y);
}

struct ClusteringAlgorithm {
	struct less {
		double *priority_of_cluster;
		less(double *priority_of_cluster = nullptr) :
				priority_of_cluster(priority_of_cluster) {
			Timer timer(__PRETTY_FUNCTION__);
		}

		bool operator ()(int x, int y) {
			return priority_of_cluster[x] < priority_of_cluster[y];
		}
	};

	ClusteringAlgorithm(Matrix &scores, const VectorI &frequency,
//			int maxNumOfClusters,
			int maxNumOfChildren) :
			scores(scores),

			n(scores.rows()),

//			maxNumOfClusters(maxNumOfClusters),

			maxNumOfChildren(std::min(maxNumOfChildren, (int) sqrt(2 * n))),

			heads(n, -1),

			num_of_children(n, 0),

			priority_of_cluster(n, 0.0),

			pq(less(&priority_of_cluster[0])) {

		for (int child = 0; child < n; ++child) {
			int parent;
			scores.col(child).maxCoeff(&parent);
			heads[child] = parent;

			++num_of_children[parent];
			priority_of_cluster[parent] += scores(parent, child);
		}
		print(num_of_children);

		double max_frequency = frequency[0];
		for (int parent = 0; parent < n; ++parent) {
			double term_weight = frequency[parent] / max_frequency;
			priority_of_cluster[parent] += 2 * term_weight * term_weight;

			pq.insert(parent);
		}
	}

	Matrix &scores;
	int n, maxNumOfChildren;
	VectorI heads;
	VectorI num_of_children;
	VectorD priority_of_cluster;
	priority_dict<int, less> pq;

	bool sanity_check() {
		bool success = true;
		for (int child = 0; child < n; ++child) {
			int parent = heads[child];
			if (parent < 0)
				continue;
			int ancestor = heads[parent];
			if (ancestor >= 0) {
				cout << "parent of " << child << " = " << parent
						<< ", parent of " << parent << " = " << ancestor
						<< endl;
				success = false;
			}
		}
		return success;
	}

	void run() {
		while (!pq.empty()) {
			int parent = pq.pop();

			print(parent);
			print(num_of_children);
			print(priority_of_cluster);
			if (parent < 0)
				continue;

			int numOfChildren = num_of_children[parent];
			print(numOfChildren);
			print(priority_of_cluster[parent]);

			if (!numOfChildren) {
//				cout << "leaf node detected, with priority = " << priority_of_cluster[parent] << endl;
				continue;
			}

			if (numOfChildren <= 2) {
//the parent of this child has too few children, so this child should abandon its current parent and find another parent!
				if (change_parent_for(find_child(parent)))
					continue;

				cout << "failed to make adjustment for " << parent << endl;
				break;
			}

			if (numOfChildren > maxNumOfChildren) {
//this parent has too many children, so this parent should abandon one of its current children and assign this abandoned child to another parent!
				if (change_parent_for(find_worst_child(parent)))
					continue;

				cout << "failed to make adjustment for " << parent << endl;
				break;
			}

			//parent should have no head, so remove its forefather
			remove_child(parent);
		}
	}

	int find_child(int parent) {
		for (int child = 0; child < n; ++child) {
			if (heads[child] == parent) {
				return child;
			}
		}
		return -1;
	}

	int find_worst_child(int parent) {
		double min_score = oo;
		int unwanted_child = -1;
		for (int child = 0; child < n; ++child) {
			if (heads[child] == parent) {
				auto _min_score = scores(parent, child);
				if (_min_score < min_score) {
					min_score = _min_score;
					unwanted_child = child;
				}
			}
		}
		return unwanted_child;
	}

	int remove_child(int child) {
		int parent = heads[child];
		if (parent >= 0) {
			auto &score = scores(parent, child);
			pq.erase(parent);
			--num_of_children[parent];
			priority_of_cluster[parent] -= score;

			score = 0;
			pq.insert(parent);

			heads[child] = -1;
		}

		return parent;
	}

	int assign_parent_for(int child) {
		int parent;
		scores.col(child).maxCoeff(&parent);
//		if (heads[child] == parent){
//			cout << "algorithm could not find a better parent" << endl;
//			return false;
//		}

		heads[child] = parent;

		pq.erase(parent);
		++num_of_children[parent];
		priority_of_cluster[parent] += scores(parent, child);

		pq.insert(parent);
		return parent;
	}

	bool change_parent_for(int child) {
		int old_parent = remove_child(child);
		int new_parent = assign_parent_for(child);
		return new_parent != old_parent;
	}
};

VectorI lexiconStructure(Matrix &scores, const VectorI &frequency,
		int maxNumOfChildren) {
	ClusteringAlgorithm cluster(scores, frequency, maxNumOfChildren);
	cluster.run();
	assert(cluster.sanity_check());
	return cluster.heads;
}

VectorI& MaskedPositions::operator()(VectorI &token,
		VectorI &masked_lm_positions) {
	for (int i = 0; i < token.size(); ++i) {
		if (token[i] < 0) {
			masked_lm_positions.push_back(i);
			token[i] = -token[i];
		}
	}
	return token;
}

Matrix MaskedGathering::operator()(const Matrix &embeddings,
		const VectorI &word) const {
	Matrix output;
	return gather(embeddings, word, output);
}

AdaptiveSoftmax::AdaptiveSoftmax(BinaryFile &dis) :
		DenseLayer(dis, Activator::log_softmax) {
	Timer timer(__PRETTY_FUNCTION__);
	print(weight.shape());
	weight.transposeInPlace();
	print(weight.shape());
	print(bias.shape());
}

VectorI ArgMaxSoftmax::operator ()(const Matrix &input_layer) {
//	Timer timer(__PRETTY_FUNCTION__);
	return argmax(input_layer);
}

VectorI& ArgMaxSoftmax::operator ()(const Matrix &input_layer,
		VectorI &output) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(input_layer);
//	print(output);
	assign(output, argmax(input_layer));
//	print(output);
	return output;
}

Matrix revert_mask(MatrixI &mask, int weight) {
	return to_matrix((1 - mask) *= weight);
}

