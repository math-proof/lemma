#pragma once
#include "../std/utility.h"
#include<vector>
using std::vector;

#include "layers.h"

#include "tokenizer.h"

struct FeedForward {
	/**
	 *
	 */

	Matrix W1, W2;
	Vector b1, b2;
	Activation activation = { Activator::relu };
	Vector& operator()(const Vector &x, Vector &ret);
	Vector operator()(const Vector &x);

	Matrix& operator()(Matrix &x, Matrix &wDense);
	Matrix operator()(const Matrix &x);

	Tensor operator()(const Tensor &x);
	vector<Vector> operator()(const vector<Vector> &x);
	FeedForward(BinaryFile &dis, bool bias = true);
	FeedForward(BinaryFile &dis, Activation activation);
	FeedForward();
};

struct LayerNormalization {
	LayerNormalization(BinaryFile &dis);
	LayerNormalization();
	void construct(BinaryFile &dis);

	const static double epsilon;
	Vector gamma, beta;

	Tensor& operator()(Tensor &x);
	Matrix& operator()(Matrix &x);
	vector<Vector>& operator()(vector<Vector> &x);
	Vector& operator()(Vector &x);
};

struct MidIndex {
//	MidIndex(int SEP = 102);
	MidIndex(int SEP);
	int SEP;
	VectorI operator()(const MatrixI &token);
	int operator()(const VectorI &token);
};

struct MaskedPositions {
	VectorI& operator()(VectorI &token, VectorI &masked_lm_positions);
};

struct MultiHeadAttention {
	MultiHeadAttention(BinaryFile &dis, int num_attention_heads);
	MultiHeadAttention();

	Matrix operator()(const Matrix &sequence);

//	cross attention only
	Matrix operator()(const Matrix &sequence, int h);

	//	cross attention only, return only the required indices;
	Matrix operator()(const Matrix &sequence, int h,
			bool return_upper_part_only);

	Matrix operator()(const Matrix &sequence, const Tensor &a_K,
			const Tensor &a_V, int max_relative_position);

	Matrix operator()(const Matrix &sequence, const Tensor &a_K,
			const Tensor &a_V, int lower, int upper, int dilation);

	//attention mask with indices provided:
	Matrix operator ()(const Matrix &sequence, const VectorI &indices);
	Matrix operator ()(const Matrix &sequence, const Tensor &a_K,
			const Tensor &a_V, const VectorI &indices);

	Vector& operator ()(const Matrix &sequence, Vector &y);

	Matrix Wq, Wk, Wv, Wo;
	Vector bq, bk, bv, bo;

	int num_attention_heads;

	Tensor& scaled_dot_product_attention(Tensor &Q, const Tensor &K,
			const Tensor &V);

	//with cross-attention-only
	Tensor& scaled_dot_product_attention(Tensor &Q, const Tensor &K,
			const Tensor &V, int h);

	//with cross-attention-only
	Tensor& scaled_dot_product_attention(Tensor &Q, const Tensor &K,
			const Tensor &V, int h, bool return_upper_part_only);

	//with max relative positional representations of k_max
	Tensor& scaled_dot_product_attention(const Tensor &Q, const Tensor &K,
			Tensor &V, const Tensor &a_K, const Tensor &a_V, int k_max);

	//with max relative positional representations of k_max
	Tensor& scaled_dot_product_attention(const Tensor &Q, const Tensor &K,
			Tensor &V, const Tensor &a_K, const Tensor &a_V, int lower, int upper, int dilation);

	//with relative positional representations
	Tensor& scaled_dot_product_attention(const Tensor &Q, const Tensor &K,
			Tensor &V, const Tensor &a_K, const Tensor &a_V);

	vector<Vector>& scaled_dot_product_attention(vector<Vector> &Q,
			const Tensor &K, const Tensor &V);

	Tensor& reshape_to_batches(Tensor &x);
	Tensor reshape_to_batches(Matrix &x);

	vector<Vector>& reshape_to_batches(vector<Vector>&);
	vector<Vector> reshape_to_batches(Vector&);

	Tensor& reshape_from_batches(Tensor&);
	vector<Vector>& reshape_from_batches(vector<Vector>&);

	static int global_dilation_hyper_parameters(int seq_length, int &lower, int &upper);
};

struct PositionEmbedding {
	PositionEmbedding(BinaryFile &dis);
	PositionEmbedding();

	void construct(BinaryFile &dis);

	int max_relative_position();

	Matrix embeddings;

	Tensor& operator()(Tensor &sequence, const VectorI &mid);
	Tensor& operator()(Tensor &sequence);
	Matrix& operator()(Matrix &sequence, int mid);
	Matrix& operator()(Matrix &sequence);
	Tensor operator ()(int seq_length);
	Tensor operator ()(int seq_length, int k_max);
	Tensor operator ()(const VectorI &indices, int k_max);
	Tensor operator ()(const VectorI &indices, int k_max, bool debug);
	Tensor operator ()(const VectorI &indices, int lower, int upper, int dilation);
	Tensor operator ()(const VectorI &r, const VectorI &d);

	MatrixI get_relative_indices(const VectorI &indices, int k_max);
	MatrixI get_relative_indices(const VectorI &indices, int lower, int upper);
	int get_relative_indices(const VectorI &indices, int lower, int upper, int x, int y);

	MatrixI get_absolute_indices(const VectorI &indices, int k_max);
	MatrixI get_absolute_indices(const VectorI &indices, int lower, int upper);

	Matrix topRows(int rows, int embed_size = -1);
	Matrix middleRows(int startRow, int n, int embed_size = -1);
	static Matrix sinusoidal_embedding(int start, int end, int embed_size);
	static int slice(int seq_length, int i, int k_max, int &start);
	static int slice(int seq_length, int i, int lower, int upper, int dilation, int &start);
	static int translate_j(int i, int j, int n, int k_max);
};

struct SegmentInput {
	MatrixI operator()(const MatrixI &token, VectorI &inputMid);
	VectorI operator()(const VectorI &token, int inputMid);
};

struct BertEmbedding {
	BertEmbedding(BinaryFile &dis, bool sinusoidal_positional_embedding);
	BertEmbedding(BinaryFile &dis);

	Embedding wordEmbedding;
	Embedding segmentEmbedding;
	PositionEmbedding positionEmbedding;
	LayerNormalization layerNormalization;
	DenseLayer embeddingMapping;

	int embed_dim();
	int hidden_size();

	Matrix operator ()(VectorI &inputToken, int inputMid,
			const VectorI &inputSegment);

	Tensor operator ()(VectorI &inputToken, int inputMid,
			const VectorI &inputSegment, bool);

	Matrix operator ()(const VectorI &inputToken, const VectorI &inputSegment);

	Matrix operator ()(const VectorI &inputToken);
};

struct SelfAttentionEncoder {
	SelfAttentionEncoder();
	SelfAttentionEncoder(BinaryFile &dis, int num_attention_heads, Activation hidden_act);

	::MultiHeadAttention MultiHeadAttention;
	LayerNormalization MultiHeadAttentionNorm;
	::FeedForward FeedForward;
	LayerNormalization FeedForwardNorm;

	Matrix& wrap_attention(Matrix &input_layer);

	//cross attention only
	Matrix& wrap_attention(Matrix &input_layer, int h);

	//cross attention only, returning only the required indices
	Matrix& wrap_attention(Matrix &input_layer, int h,
			bool return_upper_part_only);

	Matrix& wrap_attention(Matrix &input_layer, const Tensor &a_K,
			const Tensor &a_V, int max_relative_position);

	Matrix& wrap_attention(Matrix &input_layer, const Tensor &a_K,
			const Tensor &a_V, int lower, int upper, int dilation);

	//attention mask with indices provided
	Matrix& wrap_attention(Matrix &input_layer, const VectorI &indices);
	Matrix& wrap_attention(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, const VectorI &indices);

	Vector& wrap_attention(Matrix &input_layer, Vector &y);

	Tensor& wrap_feedforward(Tensor &input_layer);
	Matrix& wrap_feedforward(Matrix &input_layer);
	vector<Vector>& wrap_feedforward(vector<Vector> &input_layer);
	Vector& wrap_feedforward(Vector &input_layer);

	Matrix& operator ()(Matrix &input_layer);

//	cross-attention only
	Matrix& operator ()(Matrix &input_layer, int cross_attention_height);

	//use cross-attention only, but return only embedding of required indices
	Matrix& operator ()(Matrix &input_layer, int cross_attention_height,
			bool return_upper_part_only);

	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K,
			const Tensor &a_V, int max_relative_position);

	//a_K positional attention before softmax
	//a_V positional attention after softmax
	//lower, the maximum attention position in the former context;
	//upper, the maximum attention position in the latter context;
	//dilation, the dilation rate when taking attention in between the former and the latter context
	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, int lower, int upper, int dilation);


	//mask with only the indices provided;
	Matrix& operator ()(Matrix &input_layer, const VectorI &indices);
	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, const VectorI &indices);


	Vector& operator ()(Matrix &input_layer, Vector &y);
};

struct AlbertTransformer {
	AlbertTransformer(BinaryFile &dis, int num_hidden_layers,
			int num_attention_heads, Activation hidden_act);

	int num_hidden_layers;
	SelfAttentionEncoder encoder;

	Vector& operator ()(Matrix &input_layer, Vector &y);
	Matrix& operator ()(Matrix &input_layer);

	//cross-attention only
	Matrix& operator ()(Matrix &input_layer, int cross_attention_height);
	//cross-attention only, but return only the required indices
	Matrix& operator ()(Matrix &input_layer, int cross_attention_height,
			bool return_upper_part_only);

	//relative positional representation with band_part mask
	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K,
			const Tensor &a_V, int max_relative_position);

	//relative positional representation
	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K,
			const Tensor &a_V);
};

struct BertTransformer {
	BertTransformer(BinaryFile &dis, int num_hidden_layers,
			int num_attention_heads,
			Activation hidden_act = { Activator::gelu });
	int num_hidden_layers();
	vector<SelfAttentionEncoder> encoder;

	SelfAttentionEncoder& operator [](int i);
	Vector& operator ()(Matrix &input_layer, Vector &y);

	//relative positional representation with band_part mask
	Matrix& operator ()(Matrix &input_layer, const Tensor &a_K, const Tensor &a_V, int k_max);

	Matrix& operator ()(Matrix &input_layer, const vector<Tensor> &a_K, int lower, int upper, const VectorI &dilations);

	Matrix& operator ()(Matrix &input_layer, const vector<Tensor> &a_K, const VectorI &indices);
};

struct MaskedGathering {
	Matrix operator()(const Matrix &embedding, const VectorI &word) const;
};

struct Pairwise {
	Pairwise(BinaryFile &dis, const string &vocab, int num_attention_heads,
			bool symmetric_position_embedding = true,
			int num_hidden_layers = 12);
	FullTokenizer tokenizer;
	bool symmetric_position_embedding;

	MidIndex midIndex;
	SegmentInput segmentInput;

	BertEmbedding bertEmbedding;

	AlbertTransformer transformer;
	DenseLayer poolerDense;
	DenseLayer similarityDense;

	VectorD operator ()(MatrixI &input_ids);
	double operator ()(VectorI &input_ids);
	double operator ()(const vector<String> &s);
	double operator ()(String &x, String &y);
	double operator ()(const char16_t *x, const char16_t *y);
	static Pairwise& paraphrase();
	static Pairwise& lexicon();
};

struct PretrainingAlbert {
	PretrainingAlbert(BinaryFile &dis, Activation hidden_act,
			int num_attention_heads, int num_hidden_layers);
	BertEmbedding bertEmbedding;

	AlbertTransformer transformer;

	Vector operator ()(const VectorI &input_ids);
};

struct PretrainingAlbertChinese: PretrainingAlbert {
	PretrainingAlbertChinese(BinaryFile &dis, int num_attention_heads,
			int num_hidden_layers = 12);
	vector<String> tokenize(const String &text);
	using PretrainingAlbert::operator ();
	Vector operator ()(const String &x);
	static PretrainingAlbertChinese& instance();
};

struct PretrainingAlbertEnglish: PretrainingAlbert {
	PretrainingAlbertEnglish(BinaryFile &dis, int num_hidden_layers);
	using PretrainingAlbert::operator ();

	vector<String> tokenize(const String &text);
	Vector operator ()(const String &x);

	static PretrainingAlbertEnglish& instance();

	static PretrainingAlbertEnglish& initialize(const string &config,
			const string &path, const string &vocab);
};

struct AdaptiveSoftmax: DenseLayer {
	AdaptiveSoftmax(BinaryFile &dis);
};

struct ArgMaxSoftmax {
	VectorI operator ()(const Matrix &input_layer);
	VectorI& operator ()(const Matrix &input_layer, VectorI &output);
};

Matrix revert_mask(MatrixI &mask, int weight = 10000);
