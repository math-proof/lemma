#include "classification.h"
#include "bert.h"
#include "../std/lagacy.h"

Vector Classifier::predict(const String &predict_text) {
	auto text = predict_text;
	return predict(text);
}

Vector Classifier::predict(String &predict_text) {
//	cout << "predict: " << predict_text << endl;
	Matrix embedding;

	this->embedding(string2id(predict_text, word2id), embedding);

	Matrix lCNN;
	lCNN = con1D0(embedding, lCNN);
	lCNN = con1D1(lCNN, embedding);
	con1D2(lCNN, embedding);

	Vector x;
	lstm(embedding, x);

	dense_tanh(x);

	dense_pred(x);
//	cout << "probabilities: " << x << endl;
	return x;
}

Vector ClassifierChar::predict(const String &predict_text) {
//	cout << "predict: " << predict_text << endl;
	Matrix embedding;

	this->embedding(string2id(predict_text, word2id), embedding);

	Matrix lCNN;
	lCNN = con1D0(embedding, lCNN);
	lCNN = con1D1(lCNN, embedding);
	Vector lGRU;
	gru(lCNN, lGRU);

	return dense_pred(lGRU);
}

Vector ClassifierWord::predict(const String &predict_text) {
//	Timer timer(__PRETTY_FUNCTION__);
//	cout << "predict: " << predict_text << endl;
	Matrix embedding;

	this->embedding(string2id(tokenizer->tokenize(predict_text), word2id),
			embedding);
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix lCNN;
	lCNN = con1D0(embedding, lCNN);
	lCNN = con1D1(lCNN, embedding);
	Vector lGRU;
//	Timer timer(__PRETTY_FUNCTION__);
	return dense_pred(gru(lCNN, lGRU));
}

int Classifier::predict(const String &predict_text, int &argmax) {
	predict(predict_text).maxCoeff(&argmax);
	return argmax;
}

int ClassifierChar::predict(const String &predict_text, int &argmax) {
//	print(__PRETTY_FUNCTION__)
	predict(predict_text).maxCoeff(&argmax);
//	cout << "argmax = " << argmax << endl;
	return argmax;
}

vector<int>& ClassifierChar::predict(const vector<String> &predict_text,
		vector<int> &argmax) {
//	print(__PRETTY_FUNCTION__)
	auto size = predict_text.size();
	argmax.resize(size);
#pragma omp parallel for
	for (size_t i = 0; i < size; ++i) {
		predict(predict_text[i], argmax[i]);
	}

//	cout << "argmax = " << argmax << endl;
	return argmax;
}

int ClassifierWord::predict(const String &predict_text, int &argmax) {
//	Timer timer(__PRETTY_FUNCTION__);
	predict(predict_text).maxCoeff(&argmax);
//	print(argmax);
	return argmax;
}

vector<int>& ClassifierWord::predict(vector<String> &predict_text,
		vector<int> &argmax) {
	auto size = predict_text.size();
	argmax.resize(size);
//#pragma omp parallel for num_threads(cpu_count)
#pragma omp parallel for
	for (size_t i = 0; i < size; ++i) {
		predict(predict_text[i], argmax[i]);
	}
	return argmax;

}

vector<int>& ClassifierWord::predict(const vector<String> &predict_text,
		vector<int> &argmax) {
	auto size = predict_text.size();
	argmax.resize(size);
//#pragma omp parallel for num_threads(cpu_count)
#pragma omp parallel for
	for (size_t i = 0; i < size; ++i) {
		predict(predict_text[i], argmax[i]);
	}
	return argmax;
}

MatrixD& Classifier::predict(String &predict_text, MatrixD &arr) {
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix embedding;
	this->embedding(string2id(predict_text, word2id), embedding);

	arr.push_back(convert2vector(embedding, 0));
	arr.push_back(convert2vector(embedding, embedding.rows() - 1));

	Vector x;
	x = lstm(embedding, x, arr);
	arr.push_back(convert2vector(x));

	x = dense_tanh(x);
	arr.push_back(convert2vector(x));

	x = l2_normalize(x);
	arr.push_back(convert2vector(x));

	x = dense_pred(x);
	arr.push_back(convert2vector(x));
//	cout << arr[7] << endl;

	int index;
	x.maxCoeff(&index);

	return arr;
}

Classifier::Classifier(const string &binaryFilePath,
		const string &vocabFilePath) :
		Classifier(
				(BinaryFile&) (const BinaryFile&) BinaryFile(binaryFilePath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

ClassifierChar::ClassifierChar(const string &binaryFilePath,
		const string &vocabFilePath) :
		ClassifierChar(
				(BinaryFile&) (const BinaryFile&) BinaryFile(binaryFilePath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

ClassifierWord::ClassifierWord(const string &binaryFilePath,
		const string &vocabFilePath) :
		ClassifierWord(
				(BinaryFile&) (const BinaryFile&) BinaryFile(binaryFilePath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

Classifier::Classifier(BinaryFile &dis) :
		embedding(Embedding(dis)), con1D0(dis), con1D1(dis), con1D2(dis), lstm(
				BidirectionalLSTM(dis, Bidirectional::sum)), dense_tanh(
				DenseLayer(dis)), dense_pred(
				DenseLayer(dis, Activator::softmax)) {
	Timer timer(__PRETTY_FUNCTION__);
}

Classifier::Classifier(BinaryFile &dis, const string &vocab) :
		word2id(Text(vocab).read_vocab_char()), embedding(Embedding(dis)), con1D0(
				dis), con1D1(dis), con1D2(dis), lstm(
				BidirectionalLSTM(dis, Bidirectional::sum)), dense_tanh(
				DenseLayer(dis)), dense_pred(
				DenseLayer(dis, Activator::softmax)) {
	Timer timer(__PRETTY_FUNCTION__);
}

ClassifierChar::ClassifierChar(BinaryFile &dis, const string &vocab) :
		word2id(Text(vocab).read_vocab_char()), embedding(dis), con1D0(dis), con1D1(
				dis), gru(dis, Bidirectional::sum), dense_pred(dis,
				Activator::softmax) {
	Timer timer(__PRETTY_FUNCTION__);
}

ClassifierWord::ClassifierWord(BinaryFile &dis, const string &vocab) :
		word2id(Text(vocab).read_vocab(2)), embedding(dis), con1D0(dis), con1D1(
				dis), gru(dis, Bidirectional::sum), dense_pred(dis,
				Activator::softmax) {
	tokenizer = &FullTokenizer::instance_en();
	Timer timer(__PRETTY_FUNCTION__);
}


Classifier& Classifier::qatype_classifier() {
	Timer timer(__PRETTY_FUNCTION__);
	static Classifier service(assetsDirectory() + "cn/qatype/model.h5",
			assetsDirectory() + "cn/qatype/vocab.txt");

	return service;
}

Classifier& Classifier::phatic_classifier() {
	Timer timer(__PRETTY_FUNCTION__);
	static Classifier service(assetsDirectory() + "cn/phatic/model.h5",
			assetsDirectory() + "cn/phatic/vocab.txt");

	return service;
}

ClassifierChar& ClassifierChar::instance() {
//	Timer timer(__PRETTY_FUNCTION__);

	static ClassifierChar service(assetsDirectory() + "cn/keyword/model.bin",
			assetsDirectory() + "cn/keyword/vocab.txt");

	return service;
}

ClassifierWord& ClassifierWord::instance() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ClassifierWord service(assetsDirectory() + "en/keyword/model.bin",
			assetsDirectory() + "en/bert/albert_base/30k-clean.vocab");
//	Timer timer(__PRETTY_FUNCTION__);
	return service;
}
