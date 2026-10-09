#include "../utility.h"
#include "../../std/utility.h"
#include "CodonExtractor.h"
#include "../../std/lagacy.h"

CodonExtractor::CodonExtractor(const string &modelPath) :
		CodonExtractor((BinaryFile&) (const BinaryFile&) BinaryFile(modelPath)) {
	Timer timer(__PRETTY_FUNCTION__);
}

extern string workingDirectory;

const VectorI CodonExtractor::dilations = {1, 2, 1, 2};

CodonExtractor& CodonExtractor::instance() {
//	Timer timer(__PRETTY_FUNCTION__);
	static CodonExtractor inst(workingDirectory + "/assets/en/codon/model.bin");
	return inst;
}

Tensor CodonExtractor::operator ()(const TensorI &vocab_inputs,
		const TensorI &index_inputs, bool debug){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = vocab_inputs.size();
	Tensor res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		Matrix encoded_text_global;
		res[i] = (*this)(vocab_inputs[i], index_inputs[i], encoded_text_global);
	}

	return res;
}

TensorI CodonExtractor::operator ()(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = vocab_inputs.size();
	TensorI res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		res[i] = (*this)(vocab_inputs[i], index_inputs[i]);
	}

	return res;
}

Vector CodonExtractor::loss(const TensorI &vocab_inputs, const TensorI &index_inputs, const MatrixI &sequence_tag, const MatrixI &prev_indices, const MatrixI &relation_ptr){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = vocab_inputs.size();
	Vector res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		res[i] = loss(vocab_inputs[i], index_inputs[i], sequence_tag[i], prev_indices[i], relation_ptr[i]);
	}

	return res;
}

double CodonExtractor::loss(const MatrixI &vocab_inputs, const MatrixI &index_inputs, const VectorI &sequence_tag, const VectorI &prev_indices, const VectorI &relation_ptr){
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix encoded_text_global;
	auto encoded_text = (*this)(vocab_inputs, index_inputs, encoded_text_global);

	auto symmetricAdjacencyMatrix = this->symmetricAdjacencyMatrix(encoded_text);

	auto asymmetricAdjacencyMatrix = this->asymmetricAdjacencyMatrix(
			encoded_text_global,
			maskedGathering(encoded_text_global,
					digitMaskedPositions(vocab_inputs)));

//	encoded_text = crfDense(encoded_text);
	return symmetricDecoder.loss(symmetricAdjacencyMatrix, prev_indices) + asymmetricDecoder.loss(asymmetricAdjacencyMatrix, relation_ptr);
//	return symmetricDecoder.loss(symmetricAdjacencyMatrix, prev_indices);
//	return crf.loss(encoded_text, sequence_tag);
}

vector<Tensor> CodonExtractor::get_relative_embedding(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = vocab_inputs.size();
	vector<Tensor> res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		res[i] = get_relative_embedding(vocab_inputs[i], index_inputs[i]);
	}

	return res;
}

Tensor CodonExtractor::get_relative_embedding(const MatrixI &vocab_inputs, const MatrixI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	auto a_K = position_embedding_K(index_inputs);
	return a_K;
}

Array4I CodonExtractor::get_relative_indices(const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = index_inputs.size();
	Array4I res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		res[i] = get_relative_indices(index_inputs[i]);
	}

	return res;
}

Array4I CodonExtractor::get_absolute_indices(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	int batch_size = vocab_inputs.size();
	Array4I res(batch_size);
	for (int i = 0; i < batch_size; ++i){
		res[i] = get_absolute_indices(vocab_inputs[i], index_inputs[i]);
	}

	return res;
}

VectorI CodonExtractor::get_relative_indices(const MatrixI &index_inputs, int i, int j){
//	Timer timer(__PRETTY_FUNCTION__);
	return position_embedding_K.get_relative_indices(index_inputs, i, j);
}

TensorI CodonExtractor::get_relative_indices(const MatrixI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return position_embedding_K.get_relative_indices(index_inputs);
}

TensorI CodonExtractor::get_absolute_indices(const MatrixI &vocab_inputs, const MatrixI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return position_embedding_K.get_absolute_indices(index_inputs);
}

MatrixI CodonExtractor::operator()(const MatrixI &vocab_inputs, const MatrixI &index_inputs) {
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix encoded_text_global;
	auto encoded_text = (*this)(vocab_inputs, index_inputs, encoded_text_global);

	auto prev_indices = symmetricDecoder(symmetricAdjacencyMatrix(encoded_text));

	auto relation_ptr = asymmetricDecoder(
			asymmetricAdjacencyMatrix(
					encoded_text_global,
					maskedGathering(encoded_text_global,
							digitMaskedPositions(vocab_inputs))));

	auto sequence_tag = crf(crfDense(encoded_text));
	return {sequence_tag, prev_indices, relation_ptr};
}


vector<Tensor> CodonExtractor::relativeInformation(const MatrixI &index_inputs){
	vector<Tensor> a_K(4);
	a_K[0] = position_embedding_K(index_inputs);
	a_K[1] = position_embedding_K_2(index_inputs, 2);
	a_K[2] = a_K[0];
	a_K[3] = a_K[1];
	return a_K;
}

Matrix CodonExtractor::operator ()(const MatrixI &vocab_inputs,
		const MatrixI &index_inputs, Matrix &encoded_text_global){
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = index_inputs.size();

	auto embedding = this->embedding(vocab_inputs);

	auto outputs = this->inputDense(embedding);
	auto lCNN = this->dgluCNN(outputs);
	auto index_embedding = sinusoidalPositionEmbedding(index_inputs);

	Matrix word_embedding = lCNN + index_embedding;
	auto &encoded_text_local = localTransformer(word_embedding, relativeInformation(index_inputs), lower, upper, dilations);

	int lower, upper;
	int dilation = MultiHeadAttention::global_dilation_hyper_parameters(seq_length, lower, upper);

	Matrix encoded_text = encoded_text_local;
	encoded_text_global = globalTransformer(
			encoded_text_local,
			{position_embedding_K_global(index_inputs, -1)},
			lower,
			upper,
			{dilation});

	auto indicesGathered = headerInfoMaskedPositions(vocab_inputs);
	encoded_text_global = headerInfoTransformer(
			encoded_text_global,
			{position_embedding_K_gather(index_inputs, indicesGathered)},
			indicesGathered);

	return encoded_text += encoded_text_global;
}

CodonExtractor::CodonExtractor(BinaryFile &dis):
		embedding(dis),
		inputDense(dis),

		dgluCNN(dis),

		sinusoidalPositionEmbedding(dis),

		position_embedding_K(dis), position_embedding_K_2(dis),
		localTransformer(dis, 4, CodonExtractor::num_attention_heads,{ Activator::relu }),

		position_embedding_K_global(dis),
		globalTransformer(dis, 1, CodonExtractor::num_attention_heads,{ Activator::relu }),

		position_embedding_K_gather(dis),
		headerInfoTransformer(dis, 1, CodonExtractor::num_attention_heads,{ Activator::relu }),

		crfDense(dis),

		symmetricAdjacencyMatrix(dis, 128, 1),
		asymmetricAdjacencyMatrix(dis),

		crf(dis),

		symmetricDecoder(128, 1)
{
	Timer timer(__PRETTY_FUNCTION__);
}

const int DGLUCNN::dilations[num_convolutions] = {1, 2, 3, 2};
DGLUCNN::DGLUCNN(BinaryFile &dis){
	Timer timer(__PRETTY_FUNCTION__);
	for (int i = 0; i < num_convolutions; ++i){
		conv1d[i].construct(dis);
		layerNormalization[i].construct(dis);
	}
}


Matrix DGLUCNN::operator ()(const Matrix &x){
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix inputs = x;
	int filters = inputs.cols();

	for (int i = 0; i < num_convolutions; ++i){
		Matrix outputs;
		conv1d[i](inputs, outputs, dilations[i]);

		Matrix former = outputs.leftCols(filters);
		Matrix latter = outputs.rightCols(filters);
		inputs += former.cwiseProduct(sigmoid(latter));
		inputs = layerNormalization[i](inputs);
	}

	return inputs;
}

TabularPositionEmbedding::TabularPositionEmbedding(BinaryFile &dis){
//	Timer timer(__PRETTY_FUNCTION__);
	for (int i = 0; i < num_embeddings; ++i){
		positionEmbedding[i].construct(dis);
	}
	dis >> coefficient;	
}

VectorI TabularPositionEmbedding::max_relative_position(){
	VectorI max_relative_position(num_embeddings);
	for (int i = 0; i < num_embeddings; ++i){
		max_relative_position[i] = positionEmbedding[i].max_relative_position();
	}
	return max_relative_position;
}

Tensor TabularPositionEmbedding::operator()(const MatrixI &index_inputs, int dilation) {
//	Timer timer(__PRETTY_FUNCTION__);

	auto inputs = transpose(index_inputs);

	int lower, upper;
	if (dilation < 0){
		dilation = MultiHeadAttention::global_dilation_hyper_parameters(index_inputs.size(), lower, upper);
	}
	else{
		lower = TabularPositionEmbedding::lower;
		upper = TabularPositionEmbedding::upper;
	}

	lower *= dilation;
	upper *= dilation;

	vector<Tensor> embeddings(num_embeddings);
	for (int i = 0; i < num_embeddings; ++i){
		embeddings[i] = positionEmbedding[i](inputs[i], lower, upper, dilation);
	}

	return quadratic_form(embeddings, this->coefficient);
}

Tensor TabularPositionEmbedding::operator()(const MatrixI &index_inputs, const VectorI &indices_gathered) {
//	Timer timer(__PRETTY_FUNCTION__);

	auto inputs = transpose(index_inputs);

	vector<Tensor> embeddings(num_embeddings);
	for (int i = 0; i < num_embeddings; ++i){
		embeddings[i] = positionEmbedding[i](inputs[i], indices_gathered);
	}

	return quadratic_form(embeddings, this->coefficient);
}

TensorI TabularPositionEmbedding::get_relative_indices(const MatrixI &index_inputs) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto inputs = transpose(index_inputs);

	int depth = inputs.size();

	TensorI embeddings(depth);
	for (int i = 0; i < depth; ++i){
		embeddings[i] = positionEmbedding[i].get_relative_indices(inputs[i], lower, upper);
	}

	return embeddings;
}

VectorI TabularPositionEmbedding::get_relative_indices(const MatrixI &index_inputs, int x, int y) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto inputs = transpose(index_inputs);
	int depth = inputs.size();

	VectorI embeddings(depth);
	for (int i = 0; i < depth; ++i){
		embeddings[i] = positionEmbedding[i].get_relative_indices(inputs[i], lower, upper, x, y);
	}

	return embeddings;
}

TensorI TabularPositionEmbedding::get_absolute_indices(const MatrixI &index_inputs) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto inputs = transpose(index_inputs);

	int depth = inputs.size();

	TensorI embeddings(depth);
	for (int i = 0; i < depth; ++i){
		embeddings[i] = positionEmbedding[i].get_absolute_indices(inputs[i], lower, upper);
	}
	return embeddings;
}

MultiwayEmbedding::MultiwayEmbedding(BinaryFile &dis){
//	Timer timer(__PRETTY_FUNCTION__);
	for (int i = 0; i < num_embeddings; ++i){
		embedding[i].construct(dis);
	}
}

int MultiwayEmbedding::embed_size(){
	return embedding[0].embed_size();
}

Matrix MultiwayEmbedding::operator()(const MatrixI &vocab_inputs) {
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = vocab_inputs.size();

	auto wordsTransposed = transpose(vocab_inputs);

	int embed_size = this->embed_size();

	Matrix result = zeros(seq_length, embed_size * num_embeddings);

	for (int i = 0; i < num_embeddings; ++i){
		result.middleCols(embed_size * i, embed_size) = this->embedding[i](wordsTransposed[i]);
	}

	return result;
}

SinusoidalPositionEmbedding::SinusoidalPositionEmbedding(BinaryFile &dis){
	Timer timer(__PRETTY_FUNCTION__);
	dis >> coefficient;
}

int SinusoidalPositionEmbedding::output_dim(){
	return coefficient.cols();
}

Matrix SinusoidalPositionEmbedding::operator()(const MatrixI &index_inputs) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto embedding = PositionEmbedding::sinusoidal_embedding(0, index_inputs.size(), output_dim());
	auto inputs = transpose(index_inputs);

	int depth = inputs.size();

	Tensor embeddings(depth);
	for (int i = 0; i < depth; ++i){
		Matrix outputs;
		gather(embedding, inputs[i], outputs);
		embeddings[i] = outputs;
	}

	return quadratic_form(embeddings, this->coefficient);
}

VectorI int2bitIndices(int n){
	VectorI indices;
	while (n){
		int bsr = bsr_dword(n);
		n -= (1 << bsr);
		indices.push_back(bsr);
	}

	return indices;
}

Matrix quadratic_form(const Tensor &inputs, const Matrix &coefficient){
	auto input_shape = shape(inputs);

    int length = 1 << input_shape[0];
    int rows = input_shape[1];
    int cols = input_shape[2];
    Matrix sgm = zeros(rows, cols);

    for (int coefficient_index = 0; coefficient_index < length; ++coefficient_index){
		auto ret = int2bitIndices(coefficient_index);
		switch(ret.size()){
		case 1:{
	    	Vector row = coefficient.row(coefficient_index);
	    	Matrix mat = inputs[ret[0]];
	    	sgm += mul(mat, row);
		}
			break;
		case 2:{
	    	Vector row = coefficient.row(coefficient_index);
	    	Matrix mat = inputs[ret[0]].cwiseProduct(inputs[ret[1]]);
	    	sgm += mul(mat, row);
		}
			break;
		}
    }

    return sgm;
}

//inputs is a list of non-rectangular tensors;
Tensor quadratic_form(const vector<Tensor> &inputs, const Matrix &coefficient){
    int length = 1 << inputs.size();
    Tensor sgm;

    for (int coefficient_index = 0; coefficient_index < length; ++coefficient_index){
		auto ret = int2bitIndices(coefficient_index);
		switch (ret.size()){
		case 1:{
	    	Vector row = coefficient.row(coefficient_index);
	    	Tensor mat = inputs[ret[0]];

	    	if (sgm.size())
	    		sgm += mul(mat, row);
	    	else
	    		sgm = mul(mat, row);
		}
			break;
		case 2:{
	    	Vector row = coefficient.row(coefficient_index);
	    	Tensor mat = inputs[ret[0]];
	    	mat = mul(mat, inputs[ret[1]]);

			sgm += mul(mat, row);
		}
	    	break;
		}
    }

    return sgm;
}

AdjacencyMatrix::AdjacencyMatrix(BinaryFile &dis, int lower, int upper) :
		lower(lower),
		upper(upper),
		headArcDense(dis),
		childArcDense(dis),
		rootArcDense(dis)
{
	Timer timer(__PRETTY_FUNCTION__);
	dis >> W;
}

AsymmetricAdjacencyMatrix::AsymmetricAdjacencyMatrix(BinaryFile &dis) :
		headArcDense(dis),
		childArcDense(dis),
		rootArcDense(dis)
{
	Timer timer(__PRETTY_FUNCTION__);
	dis >> W;
}

Matrix AdjacencyMatrix::lower_triangle_adjacency_matrix(const Matrix &Q, const Matrix &K, int diagonal){
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = Q.rows();
	int breadth = std::min(lower, seq_length);

	int breadthAllocated = diagonal? breadth: breadth - 1;
	Matrix U(breadth, breadthAllocated);

	for (int i = 0; i < breadth; ++i){
		U.row(i) << ::constant(breadth - i - 1, -1e6), Q.row(i) * W * K.topRows(i + diagonal).transpose();
	}

	Matrix L(seq_length - breadth, breadthAllocated);

	for (int i: range{0, seq_length - breadth, 1}){
		L.row(i) = Q.row(i + breadth) * W * K.middleRows(i + 1, breadthAllocated).transpose();
	}

	Matrix R(seq_length, breadthAllocated);
	R << U, L;
	return R;
}

Matrix AdjacencyMatrix::upper_triangle_adjacency_matrix(const Matrix &Q, const Matrix &K){
//	Timer timer(__PRETTY_FUNCTION__);

	int seq_length = Q.rows();
	int breadth = std::min(upper, seq_length);

	Matrix U(seq_length - breadth, breadth);

	for (int i: range{0, seq_length - breadth, 1}){
		U.row(i) = Q.row(i) * W * K.middleRows(i, breadth).transpose();
	}

	Matrix L(breadth, breadth);

	for (int i = 0; i < breadth; ++i){
		L.row(i) << Q.row(i + seq_length - breadth) * W * K.bottomRows(breadth - i).transpose(), ::constant(i, -1e6);
	}

	Matrix R(seq_length, breadth);
	R << U, L;
	return R;
}

Matrix AdjacencyMatrix::operator ()(const Matrix &encoded_text){
//	Timer timer(__PRETTY_FUNCTION__);

	Matrix H;
	H = rootArcDense(encoded_text, H);

	Matrix head_arc_representation;
	head_arc_representation = headArcDense(encoded_text, head_arc_representation);

	Matrix child_arc_representation;
	child_arc_representation = childArcDense(encoded_text, child_arc_representation);

	int seq_length = head_arc_representation.rows();
	int dz = head_arc_representation.cols();
	auto ones = ::ones(seq_length, 1);

	Matrix Q(seq_length, dz + 1);
	Q << head_arc_representation, ones;

	Matrix K(seq_length, dz + 1);
	K << child_arc_representation, ones;

//	K = K.transpose();

	if (upper > 1){
		int lower_breadth = std::min(lower, seq_length);

		int breadth = std::min(lower, seq_length) + std::min(upper, seq_length) - 1;
		Matrix L = lower_triangle_adjacency_matrix(Q, K, 0);
		Matrix U = upper_triangle_adjacency_matrix(Q, K);
		Matrix R(seq_length, breadth);
		R << L, U;

		Matrix Z(seq_length, breadth);
		for (int i = 0; i < seq_length; ++i){
			int start = relu(i + 1 - lower);
			int stop = std::min(seq_length, i + upper);
			int size = stop - start;
			Vector prod = Q.row(i) * W * K.middleRows(start, size).transpose();
			prod(std::min(i, lower - 1)) += H(i);

			Z.row(i) = constant(breadth, logsumexp(prod));

			R(i, lower_breadth - 1) += H(i);
		}

		return R - Z;
	}
	else{
		int breadth = std::min(lower, seq_length);
		Matrix R = lower_triangle_adjacency_matrix(Q, K);

		Matrix Z(seq_length, breadth);
		for (int i = 0; i < seq_length; ++i){
			int start = relu(i + 1 - lower);
			int stop = i + 1;
			int size = stop - start;
			Vector prod = Q.row(i) * W * K.middleRows(start, size).transpose();
			prod(size - 1) += H(i);

			Z.row(i) = constant(breadth, logsumexp(prod));

			R(i, breadth - 1) += H(i);
		}

		return R - Z;
	}
}

Matrix AsymmetricAdjacencyMatrix::operator ()(const Matrix &encoded_text_Q, const Matrix &encoded_text_K){
//	Timer timer(__PRETTY_FUNCTION__);

	Matrix H;
	H = rootArcDense(encoded_text_Q, H);

	Matrix head_arc_representation;
	head_arc_representation = headArcDense(encoded_text_Q, head_arc_representation);

	Matrix child_arc_representation;
	child_arc_representation = childArcDense(encoded_text_K, child_arc_representation);

	int seq_length = head_arc_representation.rows();
	int dz = head_arc_representation.cols();
	Matrix Q(seq_length, dz + 1);
	Q << head_arc_representation, ::ones(seq_length, 1);

	int cols = child_arc_representation.rows();
	Matrix K(cols, dz + 1);
	K << child_arc_representation, ::ones(cols, 1);;

	Matrix attended_arcs(seq_length, cols + 1);
	attended_arcs << H, Q * W * K.transpose();
	return log_softmax(attended_arcs);
}

RelationExtractor::RelationExtractor(int lower, int upper): lower(lower), upper(upper){
}

VectorI RelationExtractor::operator ()(const Matrix &attended_arcs){
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = attended_arcs.rows();
	return argmax(attended_arcs) + 1 - std::min(lower, seq_length);
}

double RelationExtractor::loss(const Matrix &attended_arcs, const VectorI &prev_indices){
	int seq_length = prev_indices.size();
	int breadth = std::min(lower, seq_length);
	double loss = 0;
	for (int i = 0; i < seq_length; ++i){
		loss += attended_arcs(i, prev_indices[i] + breadth - 1) * (1 + log(1 + abs(prev_indices[i]) * 0.5));
	}

	return -loss / sqrt(seq_length);
}

VectorI AsymmetricRelationExtractor::operator ()(const Matrix &attended_arcs){
//	Timer timer(__PRETTY_FUNCTION__);
	return argmax(attended_arcs);
}

double AsymmetricRelationExtractor::loss(const Matrix &attended_arcs, const VectorI &prev_indices){
	int seq_length = prev_indices.size();
	double loss = 0;
	for (int i = 0; i < seq_length; ++i){
		loss += attended_arcs(i, prev_indices[i]);
	}

	return -loss / sqrt(seq_length);
}

//extract the beginning of a consecutive digit sequence
bool DigitMaskedPositions::mask_beginning_of_consecutive_digits(const MatrixI &token, int i){
	return token[i][1] == 1 && (!i || token[i - 1][1] != 1 || token[i - 1][3] != 0);
}


VectorI DigitMaskedPositions::operator()(const MatrixI &token) {
//	Timer timer(__PRETTY_FUNCTION__);
	VectorI ret;
	for (int i : range{0, (int)token.size(), 1}) {
		if (mask_beginning_of_consecutive_digits(token, i)) {
			ret.push_back(i);
		}
	}

	return ret;
}

VectorI HeaderInfoMaskedPositions::operator()(const MatrixI &token) {
//	Timer timer(__PRETTY_FUNCTION__);

	VectorI ret;
	for (int i : range{0, (int)token.size(), 1}) {
		if (DigitMaskedPositions::mask_beginning_of_consecutive_digits(token, i) || token[i][2] >= 4) {
			ret.push_back(i);
		}
	}

	return ret;
}

extern "C" {
MatrixI keras_parsers_codon_detect_en(const MatrixI &vocab_inputs, const MatrixI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return CodonExtractor::instance()(vocab_inputs, index_inputs);
}

TensorI keras_parsers_codon_detect_en_batch(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return CodonExtractor::instance()(vocab_inputs, index_inputs);
}

VectorD keras_parsers_codon_detect_en_batch_loss(const TensorI &vocab_inputs, const TensorI &index_inputs, const MatrixI &sequence_tag, const MatrixI &prev_indices, const MatrixI &relation_ptr){
//	Timer timer(__PRETTY_FUNCTION__);
	return to_double_vector(CodonExtractor::instance().loss(vocab_inputs, index_inputs, sequence_tag, prev_indices, relation_ptr));
}

TensorI keras_parsers_codon_detect_en_debug_relative_indices(const MatrixI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return CodonExtractor::instance().get_relative_indices(index_inputs);
}

VectorI keras_parsers_codon_detect_en_relative_indices(const MatrixI &index_inputs, int i, int j){
//	Timer timer(__PRETTY_FUNCTION__);
	return CodonExtractor::instance().get_relative_indices(index_inputs, i, j);
}

TensorD keras_parsers_codon_detect_en_batch_debug(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return to_double_vector(CodonExtractor::instance()(vocab_inputs, index_inputs, true));
}

vector<TensorI> keras_parsers_codon_detect_en_batch_debug_absolute_indices(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return CodonExtractor::instance().get_absolute_indices(vocab_inputs, index_inputs);
}

Array4D keras_parsers_codon_detect_en_batch_debug_relative_embedding(const TensorI &vocab_inputs, const TensorI &index_inputs){
//	Timer timer(__PRETTY_FUNCTION__);
	return to_double_vector(CodonExtractor::instance().get_relative_embedding(vocab_inputs, index_inputs));
}

void keras_parsers_codon_detect_en_init(){
//	Timer timer(__PRETTY_FUNCTION__);
	CodonExtractor::instance();
}

VectorI keras_int2bitIndices(int n){
	return int2bitIndices(n);
}
}

