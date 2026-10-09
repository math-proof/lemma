#include "POSTagger.h"
#include "../utility.h"
#include "../../std/utility.h"

MatrixI POSTagger::pos_mask(const vector<String> &pos) {
	int size = pos.size();
	MatrixI mask(size);

	int dimension = posTags.size();

	for (int i = 0; i < size; ++i) {

		int index = indexOf(posTags, pos[i]);
		if (index >= 0) {
			mask[i].resize(dimension);
			mask[i][index] = 1;
		} else {
			mask[i].assign(dimension, 1);
		}
	}
	return mask;
}

vector<String> POSTagger::convertToPOStags(const VectorI &ids) {
	int n = ids.size();
	vector<String> pos(n);
	for (int i = 0; i < n; ++i) {
		pos[i] = this->posTags[ids[i]];
	}
	return pos;
}

vector<String> POSTagger::predict(const vector<String> &predict_text) {
	auto ids = string2id(predict_text, this->word2id);
	return convertToPOStags(this->predict(ids));
}

vector<String> &POSTagger::predict(const vector<String> &predict_text, vector<String> &pos) {
	Timer timer(__PRETTY_FUNCTION__);
	auto ids = string2id(predict_text, this->word2id);

	print(ids);

	auto mask_pos = this->pos_mask(pos);
	print(mask_pos);

	pos = convertToPOStags(this->predict(ids, mask_pos));
	return pos;
}

vector<vector<String>> POSTagger::predict(
		const vector<vector<String>> &predict_text) {
	int length = predict_text.size();
	vector<vector<String>> texts(length);
	for (int i = 0; i < length; ++i) {
		if (!predict_text[i]) {
			continue;
		}
		texts[i] = this->predict(predict_text[i]);
	}
	return texts;
}

VectorI POSTagger::predict(const MatrixI &predict_text) {

	Tensor lEmbedding;
	embedding(predict_text, lEmbedding);
	int n = predict_text.size();
	Matrix wordEmbedding(n, this->embedding.wEmbedding.cols());

	for (int i = 0; i < n; ++i) {
		Vector v;
		this->gru(lEmbedding[i], v);
		wordEmbedding.row(i) = v;
	}
	Matrix ret;
	lstm0(wordEmbedding, ret);
//	cout << "ret.rows() = " << ret.rows() << endl;

	lstm1(ret, wordEmbedding);
//	cout << "wordEmbedding.rows() = " << wordEmbedding.rows() << endl;

	lstm2(wordEmbedding, ret);
//	cout << "ret.rows() = " << ret.rows() << endl;

	return wCRF(ret);
}

VectorI POSTagger::predict(const MatrixI &predict_text, const MatrixI &mask_pos) {
	Timer timer(__PRETTY_FUNCTION__);

	Tensor lEmbedding;
	embedding(predict_text, lEmbedding);
	int n = predict_text.size();
	Matrix wordEmbedding(n, this->embedding.wEmbedding.cols());

	for (int i = 0; i < n; ++i) {
		Vector v;
		this->gru(lEmbedding[i], v);
		wordEmbedding.row(i) = v;
	}
	Matrix ret;
	lstm0(wordEmbedding, ret);

	print(ret.rows());

	lstm1(ret, wordEmbedding);

	print(wordEmbedding.rows());

	lstm2(wordEmbedding, ret);

	print(ret.rows());

	return wCRF(ret, mask_pos);
}

POSTagger::POSTagger(const string &h5FilePath, const string &vocabFilePath,
		const string &posTagsFilePath) :
		POSTagger((BinaryFile&) (const BinaryFile&) BinaryFile(h5FilePath),
				vocabFilePath, posTagsFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

POSTagger::POSTagger(BinaryFile &dis, const string &vocabFilePath,
		const string &posTagsFilePath) :
		posTags(Text(posTagsFilePath).readlines()), word2id(
				Text(vocabFilePath).read_vocab_char()), embedding(dis), gru(dis,
				Bidirectional::sum), lstm0(dis, Bidirectional::sum), lstm1(dis,
				Bidirectional::sum), lstm2(dis, Bidirectional::sum), wCRF(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

//POSTagger& POSTagger::instance() {
//	static string modelFile = assetsDirectory() + "cn/pos/model.h5";
//	static string vocab = assetsDirectory() + "cn/pos/vocab.txt";
//	static string posTags = assetsDirectory() + "cn/pos/pos.txt";
//
//	static POSTagger instance(modelFile, vocab, posTags);
//
//	return instance;
//}

//POSTagger& POSTagger::instantiate() {
//	static string modelFile = assetsDirectory() + "cn/cws/model.h5";
//	static string vocab = assetsDirectory() + "cn/cws/vocab.txt";
//	static string posTags = assetsDirectory() + "cn/pos/pos.txt";
//
//	auto &instance = POSTagger::instance();
//
//	instance = POSTagger(modelFile, vocab, posTags);
//
//	return instance;
//}
