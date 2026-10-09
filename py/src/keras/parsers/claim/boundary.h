#include "../../utility.h"
#include "../../layers.h"
#pragma once

struct ParagraphBoundaryTagger {

	dict<String, int> word2id;

	Embedding word_embedding, trait_embedding;

	Conv1D<Padding::same> con1D0, con1D1, con1D2, con1D3;
	CRF wCRF;

//	int digits_begin = -1, digits_end = -1;

	MatrixI& operator()(MatrixI &input_ids, const MatrixI &trait_ids);
	VectorI& operator()(VectorI &predict_text, const VectorI &trait_ids);
	VectorI operator()(const vector<String> &predict_text,
			const VectorI &trait_ids);

	Tensor operator()(const vector<String> &predict_text, bool);
	Tensor operator()(VectorI &predict_text, bool);

	ParagraphBoundaryTagger(const string &h5FilePath,
			const string &vocabFilePath);

	ParagraphBoundaryTagger(BinaryFile &dis, const string &vocabFilePath);

	static ParagraphBoundaryTagger& instance_en();
	static ParagraphBoundaryTagger& instance_cn();
	static ParagraphBoundaryTagger& instance_tw();
	static ParagraphBoundaryTagger& instance_jp();
	static ParagraphBoundaryTagger& instance_de();
	static ParagraphBoundaryTagger& instance_kr();

	enum class Status : int {
		preamble_beg, preamble_mid, preamble_end,

		claim_beg, claim_mid, claim_end,
	};

	String convertToSegment(const vector<String> &predict_text,
			const VectorI &argmax, vector<vector<int>> &parent);

//	Matrix digits_embeddings(const VectorI &input_ids);

	static bool is_claim_number(const String &word);
};

