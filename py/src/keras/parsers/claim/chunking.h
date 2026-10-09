#include "../../utility.h"
#include "../../layers.h"
#include "../../bert.h"
#pragma once

struct SyntacticChunkingTagger {
	int k_max = 32;

	dict<String, int> word2id;

	Embedding wordEmbedding;

	Conv1D<Padding::same> conv1D0; //, conv1D1; //, conv1D2;

	PositionEmbedding a_K_embedding, a_V_embedding;

	AlbertTransformer transformer;

	LayerNormalization layerNormalization;

	CRF wCRF;

	VectorI& operator()(VectorI &predict_text);
	Tensor operator()(VectorI &predict_text, Tensor &a_K, Tensor &a_V,
			bool debug);

	MatrixI operator()(const vector<vector<String>> &predict_text);

	MatrixI operator()(const vector<vector<String>> &predict_text,
			bool parallel);

	MatrixI& operator()(MatrixI &input_ids);

	VectorI operator()(const vector<String> &predict_text);
	Tensor operator()(const vector<String> &predict_text, Tensor &a_K,
			Tensor &a_V, bool debug);

	SyntacticChunkingTagger(const string &h5FilePath,
			const string &vocabFilePath);
	SyntacticChunkingTagger(BinaryFile &dis, const string &vocabFilePath);

	static SyntacticChunkingTagger& instance_en();
	static SyntacticChunkingTagger& instance_cn();
	static SyntacticChunkingTagger& instance_tw();
	static SyntacticChunkingTagger& instance_jp();
	static SyntacticChunkingTagger& instance_kr();
	static SyntacticChunkingTagger& instance_de();

	static void test_cn();
	static void test_en();

	String convertToSegment(const vector<String> &predict_text,
			const VectorI &argmax, vector<vector<int>> &parent);
};

