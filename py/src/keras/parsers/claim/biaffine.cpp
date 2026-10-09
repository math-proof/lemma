#include "../../../std/utility.h"
#include "biaffine.h"

#include "../chu_liu_edmonds.h"

VectorI& SyntacticBiaffineParser::operator()(
		const vector<vector<String>> &texts, VectorI &chunking_tags) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	auto input_ids = string2id(texts, word2id);
//	print(input_ids);
//	print(chunking_tags);
	auto &head_indices = (*this)(input_ids, chunking_tags);

	nonprojective_adjustment(head_indices);

	return head_indices;
}

Tensor SyntacticBiaffineParser::operator()(const vector<vector<String>> &texts,
		VectorI &chunking_tags, bool debug) {
	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	auto input_ids = string2id(texts, word2id);
	print(input_ids);
	print(chunking_tags);
	return (*this)(input_ids, chunking_tags, true);
}

MatrixI& SyntacticBiaffineParser::operator()(const TensorI &texts,
		MatrixI &chunking_tags) {
//	Timer timer(__PRETTY_FUNCTION__);

	int batch_size = texts.size();
	for (int k = 0; k < batch_size; ++k) {
		(*this)(texts[k], chunking_tags[k]);
	}

	return numpify(chunking_tags);
}

MatrixI& SyntacticBiaffineParser::operator()(const TensorI &texts,
		MatrixI &chunking_tags, bool parallel) {
//	Timer timer(__PRETTY_FUNCTION__);

	int batch_size = texts.size();
#pragma omp parallel for
	for (int k = 0; k < batch_size; ++k) {
		(*this)(texts[k], chunking_tags[k]);
	}

	return numpify(chunking_tags);
}

VectorI& SyntacticBiaffineParser::operator()(const MatrixI &input_ids,
		VectorI &chunking_tags) {
//	Timer timer(__PRETTY_FUNCTION__);

	auto embedding_output = wordEmbedding(input_ids);
	Matrix gru_layer;
	this->gru(embedding_output, gru_layer);

	auto pos_tag_layer = this->pos_tag_embedding(chunking_tags);

	auto chunk_embedding = gru_layer + pos_tag_layer;

	auto cnn_layer = conv1D2(conv1D1(conv1D0(chunk_embedding)));

	Matrix lstm_layer_0;
	this->lstm0(cnn_layer, lstm_layer_0);
	Matrix lstm_layer;
	this->lstm1(lstm_layer_0, lstm_layer);

	Matrix head_arc_representation;
	this->headArcDense(lstm_layer, head_arc_representation);

	auto child_arc_representation = this->childArcDense(lstm_layer);

	auto arc_attention = this->bilinearMatrixAttention(head_arc_representation,
			child_arc_representation);

	return this->structureDecoder(arc_attention, chunking_tags);
}

Tensor SyntacticBiaffineParser::operator()(const MatrixI &input_ids,
		VectorI &chunking_tags, bool debug) {
	Tensor result;
//	Timer timer(__PRETTY_FUNCTION__);

	auto embedding_output = wordEmbedding(input_ids);
	Matrix gru_layer;
	this->gru(embedding_output, gru_layer);
	result.push_back(gru_layer);

	auto pos_tag_layer = this->pos_tag_embedding(chunking_tags);
	result.push_back(pos_tag_layer);

	auto chunk_embedding = gru_layer + pos_tag_layer;
	result.push_back(chunk_embedding);

	auto cnn_layer = conv1D2(conv1D1(conv1D0(chunk_embedding)));
	result.push_back(cnn_layer);

	Matrix lstm_layer_0;
	this->lstm0(cnn_layer, lstm_layer_0);
	result.push_back(lstm_layer_0);

	Matrix lstm_layer;
	this->lstm1(lstm_layer_0, lstm_layer);
	result.push_back(lstm_layer);

	Matrix head_arc_representation;
	this->headArcDense(lstm_layer, head_arc_representation);
	result.push_back(head_arc_representation);

	auto child_arc_representation = this->childArcDense(lstm_layer);
	result.push_back(child_arc_representation);

	auto arc_attention = this->bilinearMatrixAttention(head_arc_representation,
			child_arc_representation);

	result.push_back(arc_attention);

	auto &head_indices = this->structureDecoder(arc_attention, chunking_tags);

	result.push_back(unsqueeze(head_indices));
	return result;
}

SyntacticBiaffineParser::SyntacticBiaffineParser(const string &h5FilePath,
		const string &vocabFilePath) :
		SyntacticBiaffineParser(
				(BinaryFile&) (const BinaryFile&) BinaryFile(h5FilePath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

SyntacticBiaffineParser::SyntacticBiaffineParser(BinaryFile &dis,
		const string &vocabFilePath) :
		word2id(Text(vocabFilePath).read_vocab()),

		wordEmbedding(dis),

		gru(dis, Bidirectional::sum),

		pos_tag_embedding(dis),

		conv1D0(dis), conv1D1(dis), conv1D2(dis),

		lstm0(dis, Bidirectional::sum), lstm1(dis, Bidirectional::sum),

		headArcDense(dis), childArcDense(dis),

		bilinearMatrixAttention(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_en() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "en/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "en/parsers/claim/biaffine/vocab.txt");
	return inst;
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_cn() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "cn/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "cn/parsers/claim/biaffine/vocab.txt");
	return inst;
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_tw() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "tw/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "tw/parsers/claim/biaffine/vocab.txt");
	return inst;
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_jp() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "jp/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "jp/parsers/claim/biaffine/vocab.txt");
	return inst;
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_kr() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "kr/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "kr/parsers/claim/biaffine/vocab.txt");
	return inst;
}

SyntacticBiaffineParser& SyntacticBiaffineParser::instance_de() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticBiaffineParser inst(
			assetsDirectory() + "de/parsers/claim/biaffine/model.bin",
			assetsDirectory() + "de/parsers/claim/biaffine/vocab.txt");
	return inst;
}

void SyntacticBiaffineParser::test_cn() {
	vector<std::string> claim_text = { };

//	Tensor tmp;
//	print(instance_cn()(std::toStrings(claim_text), tmp, tmp, true));
}

void SyntacticBiaffineParser::test_en() {
	vector<vector<string>> text = { { "13", ".", "an", "operating", "method",
			"of", "a", "projector", ",", "the", "operating", "method",
			"comprising", ":", "\\n" }, { "generating", "a", "plurality", "of",
			"subframe", "videos", "from", "an", "input", "video", ";", "\\n" },
			{ "controlling", "a", "digital", "micromirror", "device", "of",
					"the", "projector", "to", "sequentially", "projecting",
					"frames", "of", "the", "plurality", "of", "subframe",
					"videos", ";", "and", "\\n" }, { "controlling", "an",
					"actuator", "assembly", "of", "the", "projector", "to",
					"project", "the", "plurality", "of", "subframe", "videos",
					"at", "different", "optical", "angles", ",", "\\n",
					"wherein" }, { "the", "actuator", "assembly", "comprises" },
			{ "a", "first", "glass", "tilted", "in", "a", "first", "direction",
					"and", "a", "second", "glass", "tilted", "in", "a",
					"second", "direction", "perpendicular", "to", "the",
					"first", "direction", ",", "and", "the", "controlling",
					"of", "the", "actuator", "assembly", "comprises" }, {
					"controlling", "the", "first", "glass", "and", "the",
					"second", "glass", "such", "that", "at", "least", "one",
					"of", "the", "first", "glass", "and", "the", "second",
					"glass", "is", "tilted", "or", "is", "not", "tilted",
					"when", "each", "of", "the", "plurality", "of", "subframe",
					"videos", "is", "projected", ".", "\\n" } };
	VectorI posTag = { 0, 1, 1, 0, 0, 0, 1 };

	auto &model = SyntacticBiaffineParser::instance_en();
	auto head_indices = model(std::toStrings(text), posTag, true);
//	print(head_indices);
}

#include "../chu_liu_edmonds.h"

VectorI& StructureDecoder::operator ()(Matrix &attended_arcs,
		VectorI &chunking_tags) {
//	Mask the diagonal, because the head of a word can't be itself.
	double inf = 100000.0;
	int seq_length = attended_arcs.rows();
	for (int i = 0; i < seq_length; ++i) {
		attended_arcs(i, i) -= inf;
	}

	softmax(attended_arcs);
	cast_to_floats(attended_arcs);
	attended_arcs.transposeInPlace();

	//    # Although we need to include the root node so that the MST includes it,
	//    # we do not want any word to be the parent of the root node.
	//    # Here, we enforce this by setting the scores for all word -> ROOT edges
	//    # edges to be 0.
	Vector zeros_vector = zeros(seq_length);

	attended_arcs.row(0) = zeros_vector;
// upper-triangularized
	linalg_band_part(attended_arcs, 0, -1);

	for (int j = 0; j < seq_length; ++j) {
		if (chunking_tags[j]) {
//if it is a leaf node, it mustn't be a parent of any other node.
//chunking_tags[j] = 1, hence j is the leaf node
			attended_arcs.row(j) = zeros_vector;
		} else {
//if it is an internal node, its next sibling must be its child.
//chunking_tags[j] = 0, hence j is the parent / internal node, its next sibling is j + 1
// the parent of j + 1 must be j, so ForAll[i != j] attended_arcs(i, j + 1) = 0;
			for (int i = 0; i < seq_length; ++i) {
				if (i != j) {
//here we are sure that j + 1 < seq_length because the last node must be a leaf node,
//hence a parent / internal node can't be the last node!
					attended_arcs(i, j + 1) = 0;
				}
//				else{
//					attended_arcs(j, j + 1) = attended_arcs(j, j + 1);
//				}
			}
		}
	}

	return decode_mst(attended_arcs, chunking_tags);
}

/*
 vector<Tensor> SyntacticBiaffineParser::operator()(const TensorI &input_ids,
 MatrixI &chunking_tags, bool debug) {

 return batch_write(input_ids.size(), [&](int k) {
 return (*this)(input_ids[k], chunking_tags[k], true);
 });
 }
 */

extern "C" {
MatrixI keras_parsers_claim_biaffine_cn(TensorI &text, MatrixI &chunking_tags) {
//	Timer timer(__PRETTY_FUNCTION__);

	strip_tailing_zeros(text);
	strip_tailing_zeros(chunking_tags);
	return SyntacticBiaffineParser::instance_cn()(text, chunking_tags);
}

MatrixI keras_parsers_claim_biaffine_en(TensorI &text, MatrixI &chunking_tags) {
//	Timer timer(__PRETTY_FUNCTION__);

	strip_tailing_zeros(text);
	strip_tailing_zeros(chunking_tags);
	return SyntacticBiaffineParser::instance_en()(text, chunking_tags);
}

int keras_parsers_is_licit_claim_tree(const VectorI &chunking_tags,
		const VectorI &head_indices) {
//	Timer timer(__PRETTY_FUNCTION__);
	//sizes mismatch
	if (chunking_tags.size() != head_indices.size())
		return 1;

	if (is_projective(head_indices))
		return 2;

	std::set<int> parent_set(head_indices.begin(), head_indices.end());

	int n = chunking_tags.size();
	for (int i = 0; i < n; ++i) {
		if (chunking_tags[i]) {
			//it is a leaf node, it must have a parent;
			if (head_indices[i] < 0)
				return 3;
			//it mustn't be a parent of any other node!
			if (parent_set.count(i))
				return 4;
		} else {
			//since it is an internal node, it must have a child;
			if (!parent_set.count(i))
				return 5;
			//since it is an internal node, it must have a sibling;
			if (i + 1 >= n)
				return 6;
			//since it is an internal node, its next sibling must be its child;
			if (head_indices[i + 1] != i)
				return 7;

		}
	}
//	0 indicates a licit result
	return 0;
}

}

