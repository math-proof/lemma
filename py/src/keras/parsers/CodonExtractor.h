#include "../utility.h"
#include "../layers.h"
#include "../bert.h"

Matrix quadratic_form(const Tensor &inputs, const Matrix &coefficient);
Tensor quadratic_form(const vector<Tensor> &inputs, const Matrix &coefficient);

struct MultiwayEmbedding{
	static constexpr int num_embeddings = 4;
	Embedding embedding[num_embeddings];
	MultiwayEmbedding(BinaryFile &dis);

	int embed_size();
	//shape = seq_length, embed_size * num_embeddings;
	Matrix operator()(const MatrixI &vocab_inputs);
};

struct DGLUCNN{
	static constexpr int num_convolutions = 4;
	static const int dilations[num_convolutions];
	DGLUCNN(BinaryFile &dis);
	Conv1D<Padding::same> conv1d[num_convolutions];
	LayerNormalization layerNormalization[num_convolutions];
	Matrix operator ()(const Matrix &x);
};

struct SinusoidalPositionEmbedding{
	Matrix coefficient;
//	shape = (32, 64)
	int output_dim();
	SinusoidalPositionEmbedding(BinaryFile &dis);
	Matrix operator()(const MatrixI &index_inputs);
};

struct TabularPositionEmbedding {
	static constexpr int num_embeddings = 5;
	static constexpr int num_attention_heads = 8;

	static constexpr int lower = 72;
	static constexpr int upper = 64;

	PositionEmbedding positionEmbedding[num_embeddings];
	Matrix coefficient;
//	shape = (32, 16)
	TabularPositionEmbedding(BinaryFile &dis);
	VectorI max_relative_position();
	Tensor operator()(const MatrixI &index_inputs, int dilation = 1);
	Tensor operator()(const MatrixI &index_inputs, const VectorI &indices_gathered);
	TensorI get_relative_indices(const MatrixI &index_inputs);
	TensorI get_absolute_indices(const MatrixI &index_inputs);
	VectorI get_relative_indices(const MatrixI &index_inputs, int x, int y);
};

struct AdjacencyMatrix {
	const int lower;
	const int upper;

	DenseLayer headArcDense;
	DenseLayer childArcDense;
	DenseLayer rootArcDense;

	Matrix W;
	AdjacencyMatrix(BinaryFile &dis, int lower, int upper);
	Matrix operator()(const Matrix &encoded_text);
	Matrix lower_triangle_adjacency_matrix(const Matrix &Q, const Matrix &K, int diagonal = 1);
	Matrix upper_triangle_adjacency_matrix(const Matrix &Q, const Matrix &K);
};

struct AsymmetricAdjacencyMatrix {
	DenseLayer headArcDense;
	DenseLayer childArcDense;
	DenseLayer rootArcDense;

	Matrix W;
	AsymmetricAdjacencyMatrix(BinaryFile &dis);
	Matrix operator()(const Matrix &Q, const Matrix &K);
};

struct RelationExtractor {
	const int lower;
	const int upper;
	RelationExtractor(int lower, int upper);
	VectorI operator()(const Matrix &attended_arcs);
	double loss(const Matrix &attended_arcs, const VectorI &prev_indices);
};

struct AsymmetricRelationExtractor {
	VectorI operator()(const Matrix &attended_arcs);
	double loss(const Matrix &attended_arcs, const VectorI &prev_indices);
};

struct DigitMaskedPositions {
	VectorI operator()(const MatrixI &token);

	static bool mask_beginning_of_consecutive_digits(const MatrixI &vocab_inputs, int i);
};

struct HeaderInfoMaskedPositions {
	VectorI operator()(const MatrixI &token);
};

struct CodonExtractor {
	static constexpr int num_attention_heads = TabularPositionEmbedding::num_attention_heads;
	static const VectorI dilations;
	static constexpr int lower = TabularPositionEmbedding::lower;
	static constexpr int upper = TabularPositionEmbedding::upper;

	vector<Tensor> relativeInformation(const MatrixI &index_inputs);

	MultiwayEmbedding embedding;
	DenseLayer inputDense;

	DGLUCNN dgluCNN;
	SinusoidalPositionEmbedding sinusoidalPositionEmbedding;

	TabularPositionEmbedding position_embedding_K, position_embedding_K_2;
	BertTransformer localTransformer;

	TabularPositionEmbedding position_embedding_K_global;
	BertTransformer globalTransformer;

	TabularPositionEmbedding position_embedding_K_gather;
	BertTransformer headerInfoTransformer;

	DenseLayer crfDense;

	AdjacencyMatrix symmetricAdjacencyMatrix;

	HeaderInfoMaskedPositions headerInfoMaskedPositions;
	DigitMaskedPositions digitMaskedPositions;

	MaskedGathering maskedGathering;
	AsymmetricAdjacencyMatrix asymmetricAdjacencyMatrix;

	CRF crf;
	RelationExtractor symmetricDecoder;
	AsymmetricRelationExtractor asymmetricDecoder;

	MatrixI operator ()(const MatrixI &ascii_inputs, const MatrixI &index_inputs);

	TensorI operator ()(const TensorI &ascii_inputs, const TensorI &index_inputs);

	Matrix operator ()(const MatrixI &ascii_inputs, const MatrixI &index_inputs, Matrix &encoded_text_global);

	Matrix operator ()(const MatrixI &ascii_inputs, const MatrixI &index_inputs, Matrix &encoded_text_global, bool debug);

	Tensor operator ()(const TensorI &ascii_inputs, const TensorI &index_inputs, bool debug);

	Vector loss(const TensorI &ascii_inputs, const TensorI &index_inputs, const MatrixI &sequence_tag, const MatrixI &prev_indices, const MatrixI &relation_ptr);

	double loss(const MatrixI &ascii_inputs, const MatrixI &index_inputs, const VectorI &sequence_tag, const VectorI &prev_indices, const VectorI &relation_ptr);

	static CodonExtractor& instance();

	Array4I get_relative_indices(const TensorI &index_inputs);
	TensorI get_relative_indices(const MatrixI &index_inputs);
	VectorI get_relative_indices(const MatrixI &index_inputs, int i, int j);

	Array4I get_absolute_indices(const TensorI &ascii_inputs, const TensorI &index_inputs);
	TensorI get_absolute_indices(const MatrixI &ascii_inputs, const MatrixI &index_inputs);

	vector<Tensor> get_relative_embedding(const TensorI &ascii_inputs, const TensorI &index_inputs);
	Tensor get_relative_embedding(const MatrixI &ascii_inputs, const MatrixI &index_inputs);

	CodonExtractor(const string &modelPath);
	CodonExtractor(BinaryFile &dis);
};
