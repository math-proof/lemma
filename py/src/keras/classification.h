#pragma once

#include "layers.h"
#include "matrix.h"

struct Classifier {
	dict<char16_t, int> word2id;
	Embedding embedding;
	Conv1D<Padding::same> con1D0, con1D1, con1D2;
	BidirectionalLSTM lstm;
	DenseLayer dense_tanh, dense_pred;

	Vector predict(const String &predict_text);
	Vector predict(String &predict_text);
	int predict(const String &predict_text, int &argmax);

	MatrixD& predict(String &predict_text,
			MatrixD &arr);

	Classifier(const string &binaryFilePath, const string &vocabFilePath);
	Classifier(BinaryFile &dis);
	Classifier(BinaryFile &dis, const string &vocab);

	TensorD& weight(TensorD &arr);

	static Classifier& phatic_classifier();
	static Classifier& qatype_classifier();
};

struct ClassifierChar {
	dict<char16_t, int> word2id;
	Embedding embedding;
	Conv1D<Padding::same> con1D0, con1D1;
	BidirectionalGRU gru;
	DenseLayer dense_pred;

	Vector predict(const String &predict_text);
	int predict(const String &predict_text, int &argmax);
	vector<int>& predict(const vector<String> &predict_text,
			vector<int> &argmax);

	MatrixD& predict(String &predict_text,
			MatrixD &arr);

	ClassifierChar(const string &binaryFilePath, const string &vocabFilePath);
	ClassifierChar(BinaryFile &dis, const string &vocab);

	TensorD& weight(TensorD &arr);

	static ClassifierChar& instance();
};

#include "tokenizer.h"

struct ClassifierWord {
	dict<String, int> word2id;
	Embedding embedding;
	Conv1D<Padding::same> con1D0, con1D1;
	BidirectionalGRU gru;
	DenseLayer dense_pred;

	FullTokenizer *tokenizer;

	Vector predict(const String &predict_text);

	int predict(const String &predict_text, int &argmax);

	vector<int>& predict(const vector<String> &predict_text,
			vector<int> &argmax);

	vector<int>& predict(vector<String> &predict_text,
			vector<int> &argmax);

	MatrixD& predict(String &predict_text,
			MatrixD &arr);

	ClassifierWord(const string &binaryFilePath, const string &vocabFilePath);
	ClassifierWord(BinaryFile &dis, const string &vocab);

	TensorD& weight(TensorD &arr);

	static ClassifierWord& instance();
};

