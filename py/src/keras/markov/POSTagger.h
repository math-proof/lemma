#include "../utility.h"
#include "../layers.h"
#pragma once
struct POSTagger {
	vector<String> convertToPOStags(const VectorI &ids);
	vector<String> posTags;
	dict<char16_t, int> word2id;
	Embedding embedding;
	BidirectionalGRU gru;
	BidirectionalLSTM lstm0, lstm1, lstm2;
	CRF wCRF;

	VectorI predict(const MatrixI &predict_text);
	VectorI predict(const MatrixI &predict_text, const MatrixI &mask_pos);
	vector<String> predict(const vector<String> &predict_text);
	vector<String>& predict(const vector<String> &predict_text,
			vector<String> &pos);

	vector<vector<String>> predict(const vector<vector<String>> &predict_text);

	POSTagger(const string &h5FilePath, const string &vocabFilePath,
			const string &posTagsFilePath);
	POSTagger(BinaryFile &dis, const string &vocabFilePath,
			const string &posTagsFilePath);

	MatrixI pos_mask(const vector<String> &pos);

	static POSTagger& instance();
	static POSTagger& instantiate();
};

