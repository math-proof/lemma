#include "../../utility.h"
#include "../../layers.h"
#include "../../bert.h"

struct StructureDecoder {
	VectorI& operator ()(Matrix &x, VectorI &chunking_tags);
	VectorI& operator ()(Matrix &x, VectorI &chunking_tags, bool debug);
};

struct SyntacticBiaffineParser {
	dict<String, int> word2id;

	Embedding wordEmbedding;

	BidirectionalGRU gru;

	Embedding pos_tag_embedding;

	Conv1D<Padding::same> conv1D0, conv1D1, conv1D2;

	BidirectionalLSTM lstm0, lstm1;

	DenseLayer headArcDense, childArcDense;

	BilinearMatrixAttention bilinearMatrixAttention;

	StructureDecoder structureDecoder;

	Tensor operator()(const MatrixI &input_ids, VectorI &pos_tags, bool debug);

//	vector<Tensor> operator()(const TensorI &input_ids, MatrixI &pos_tags,
//			bool debug);

	MatrixI& operator()(const TensorI &input_ids, MatrixI &pos_tags);

	MatrixI& operator()(const TensorI &input_ids, MatrixI &pos_tags,
			bool parallel);

	VectorI& operator()(const MatrixI &input_ids, VectorI &pos_tags);

	VectorI& operator()(const vector<vector<String>> &text, VectorI &pos_tags);

	Tensor operator()(const vector<vector<String>> &text, VectorI &pos_tags,
			bool debug);

	SyntacticBiaffineParser(const string &h5FilePath,
			const string &vocabFilePath);
	SyntacticBiaffineParser(BinaryFile &dis, const string &vocabFilePath);

	static SyntacticBiaffineParser& instance_en();
	static SyntacticBiaffineParser& instance_cn();
	static SyntacticBiaffineParser& instance_tw();
	static SyntacticBiaffineParser& instance_jp();
	static SyntacticBiaffineParser& instance_kr();
	static SyntacticBiaffineParser& instance_de();

	static void test_cn();
	static void test_en();
};

