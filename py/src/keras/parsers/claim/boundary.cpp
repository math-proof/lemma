#include "../claim/boundary.h"

String ParagraphBoundaryTagger::convertToSegment(
		const vector<String> &predict_text, const VectorI &argmax,
		vector<vector<int>> &parent) {
	vector<String> texts;
	String sstr;

	String content = u"";
	assert((size_t ) argmax.size() == predict_text.size());
	for (int i = 0, size = argmax.size(); i < size; ++i) {
		content += predict_text[i];

		switch ((Status) argmax[i]) {
		case Status::preamble_end:
		case Status::claim_end:
//		case Status::missing_end:
			texts.push_back(content);
			content.clear();
			break;
		default:
			;
		}
	}

	if (content.size()) {
		texts.push_back(content);
	}

	int start;
	String infix;
	if (argmax[0] == 0) {
		infix = u"{" + texts[0] + u"}";
		start = 1;
	} else {
		infix = u"{}";
		start = 0;
	}

	for (int i = start; i < texts.size(); ++i) {
		infix += u"{" + texts[i] + u"}";
	}

	parent.resize(texts.size() - start);
	return infix;
}

VectorI ParagraphBoundaryTagger::operator()(const vector<String> &predict_text,
		const VectorI &trait_ids) {
//	Timer timer(__PRETTY_FUNCTION__);
	VectorI input_ids = string2id(predict_text, word2id);
//	print(input_ids);
//	print(trait_ids);
	return (*this)(input_ids, trait_ids);
}

MatrixI& ParagraphBoundaryTagger::operator()(MatrixI &input_ids,
		const MatrixI &trait_ids) {
	int batch_size = input_ids.size();

#pragma omp parallel for
	for (int k = 0; k < batch_size; ++k) {
		(*this)(input_ids[k], trait_ids[k]);
	}

	return input_ids;
}

Tensor ParagraphBoundaryTagger::operator()(const vector<String> &predict_text,
		bool) {
	VectorI input_ids = string2id(predict_text, word2id);
	print(input_ids);
	return (*this)(input_ids, true);
}

//Matrix ParagraphBoundaryTagger::digits_embeddings(const VectorI &input_ids) {
//	int size = input_ids.size();
//	VectorI digits_ids(size);
//	for (int i = 0; i < size; ++i) {
//		int index = input_ids[i];
//		digits_ids[i] = index >= digits_begin && index < digits_end;
//	}
//
//	Matrix lEmbedding;
//	digits_embedding(digits_ids, lEmbedding, true);
//	return lEmbedding;
//}

VectorI& ParagraphBoundaryTagger::operator()(VectorI &input_ids,
		const VectorI &trait_ids) {
//	Timer timer(__PRETTY_FUNCTION__);

	Matrix lEmbedding;
	word_embedding(input_ids, lEmbedding, true);
	lEmbedding += trait_embedding(trait_ids, true);

//	print(lEmbedding);
	Matrix cnn;
	con1D0(lEmbedding, cnn, true);
//	print(cnn);

	con1D1(cnn, lEmbedding, 2, true);
//	print(lEmbedding);

	con1D2(lEmbedding, cnn, true);
//	print(cnn);

	con1D3(cnn, lEmbedding, 2, true);
//	print(lEmbedding);

	return wCRF(lEmbedding, input_ids);
}

Tensor ParagraphBoundaryTagger::operator()(VectorI &input_ids, bool) {
//	Timer timer(__PRETTY_FUNCTION__);

	Tensor result;
	Matrix lEmbedding;
	word_embedding(input_ids, lEmbedding);
	result.push_back(lEmbedding);

//	lEmbedding += digits_embeddings(input_ids);
//	result.push_back(lEmbedding);

	Matrix cnn;
	con1D0(lEmbedding, cnn);
	result.push_back(cnn);

	con1D1(cnn, lEmbedding);
	result.push_back(lEmbedding);

	con1D2(lEmbedding, cnn);
	result.push_back(cnn);

	print(wCRF(cnn, input_ids));
	return result;
}

ParagraphBoundaryTagger::ParagraphBoundaryTagger(const string &modelPath,
		const string &vocabFilePath) :
		ParagraphBoundaryTagger(
				(BinaryFile&) (const BinaryFile&) BinaryFile(modelPath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

ParagraphBoundaryTagger::ParagraphBoundaryTagger(BinaryFile &dis,
		const string &vocabFilePath) :
		word2id(Text(vocabFilePath).read_vocab()),

		word_embedding(dis), trait_embedding(dis),

		con1D0(dis), con1D1(dis), con1D2(dis), con1D3(dis),

		wCRF(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

bool ParagraphBoundaryTagger::is_claim_number(const String &word) {
//	Timer timer(__PRETTY_FUNCTION__);
	if (word.size() > 3)
		return false;
	for (auto ch : word) {
		if (isdigit(ch))
			continue;
		return false;
	}
	return true;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_en() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "en/parsers/claim/boundary/model.bin",
			assetsDirectory() + "en/parsers/claim/boundary/vocab.txt");
	return inst;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_cn() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "cn/parsers/claim/boundary/model.bin",
			assetsDirectory() + "cn/parsers/claim/boundary/vocab.txt");
	return inst;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_tw() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "tw/parsers/claim/boundary/model.bin",
			assetsDirectory() + "tw/parsers/claim/boundary/vocab.txt");
	return inst;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_jp() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "jp/parsers/claim/boundary/model.bin",
			assetsDirectory() + "jp/parsers/claim/boundary/vocab.txt");
	return inst;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_kr() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "kr/parsers/claim/boundary/model.bin",
			assetsDirectory() + "kr/parsers/claim/boundary/vocab.txt");
	return inst;
}

ParagraphBoundaryTagger& ParagraphBoundaryTagger::instance_de() {
//	Timer timer(__PRETTY_FUNCTION__);
	static ParagraphBoundaryTagger inst(
			assetsDirectory() + "de/parsers/claim/boundary/model.bin",
			assetsDirectory() + "de/parsers/claim/boundary/vocab.txt");
	return inst;
}

MatrixI keras_parsers_claim_boundary(ParagraphBoundaryTagger &model,
		MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	strip_tailing_zeros(text);
	strip_tailing_zeros(trait);

	return numpify(model(text, trait));
}

extern "C" {

MatrixI keras_parsers_claim_boundary_cn(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_cn(),
			text, trait);
}

MatrixI keras_parsers_claim_boundary_tw(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_tw(),
			text, trait);
}

MatrixI keras_parsers_claim_boundary_jp(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_jp(),
			text, trait);
}

MatrixI keras_parsers_claim_boundary_kr(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_kr(),
			text, trait);
}

MatrixI keras_parsers_claim_boundary_de(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_de(),
			text, trait);
}

MatrixI keras_parsers_claim_boundary_en(MatrixI &text, MatrixI &trait) {
//	Timer timer(__PRETTY_FUNCTION__);
	return keras_parsers_claim_boundary(ParagraphBoundaryTagger::instance_en(),
			text, trait);
}

}
