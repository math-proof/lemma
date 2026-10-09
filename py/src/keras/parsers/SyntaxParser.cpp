#include "SyntaxParser.h"
#include "../utility.h"
#include "../../std/utility.h"

vector<String> SyntaxParser::convertToDEPtags(const VectorI &ids) {
	int n = ids.size();
	vector<String> dep(n);
//	print(ids);
//	print(depTags);
	for (int i = 0; i < n; ++i) {
		dep[i] = depTags[ids[i]];
	}
	return dep;
}

VectorI SyntaxParser::operator()(const vector<String> &seg,
		const vector<String> &pos, vector<String> &dep) {
//	Timer timer(__PRETTY_FUNCTION__);

//	print(seg);
//	print(pos);
//	cout << "vocab.size() = " << vocab.size() << endl;
//	cout << "posTags.size() = " << posTags.size() << endl;

	auto seg_ids = string2id(seg, this->vocab);
	auto pos_ids = string2id(pos, this->posTags);
	VectorI dep_ids;
//	cout << "seg_ids = " << seg_ids << endl;
//	cout << "pos_ids = " << pos_ids << endl;
	VectorI heads;
	heads = this->model(seg_ids, pos_ids, dep_ids, heads);

	for (auto &id : heads) {
		--id;
	}

	dep = this->convertToDEPtags(dep_ids);
	return heads;
}

VectorI& SyntaxParser::operator()(const vector<String> &seg,
		const vector<String> &pos, vector<String> &dep, VectorI &heads) {
//	Timer timer(__PRETTY_FUNCTION__);

//	print(seg);
//	print(pos);
//	print(heads);
//	print(vocab.size());
//	print(posTags.size());

	auto seg_ids = string2id(seg, this->vocab);
	auto pos_ids = string2id(pos, this->posTags);
	VectorI dep_ids;

//	print(seg_ids);
//	print(pos_ids);

	for (auto &id : heads) {
		++id;
	}

//	print(heads);

	heads = this->model(seg_ids, pos_ids, dep_ids, heads);

//	print(heads);
	for (auto &id : heads) {
		--id;
	}
//	print(heads);

	dep = this->convertToDEPtags(dep_ids);
	return heads;
}

VectorI& BiaffineDependencyParser::operator()(const VectorI &seg,
		const VectorI &pos, VectorI &predicted_head_tags,
		VectorI &predicted_heads) {
//	Timer timer(__PRETTY_FUNCTION__);

	int seq_length = seg.size();
	auto segEmbedding = text_field_embedder(seg);
	auto posEmbedding = _pos_tag_embedding(pos);

	Matrix embedded_text_input(seq_length, segEmbedding.cols() + posEmbedding.cols());
	embedded_text_input << segEmbedding, posEmbedding;

//	print(embedded_text_input);

	auto &_encoded_text = encoder(embedded_text_input);
	Matrix encoded_text(seq_length + 1, _encoded_text.cols());

//	print_shape(_head_sentinel);
//	print(_head_sentinel);
//	print(_encoded_text);

	encoded_text << _head_sentinel, _encoded_text;

//	print_shape(encoded_text);

	Matrix head_arc_representation, child_arc_representation,
			head_tag_representation, child_tag_representation;

//	print(encoded_text);
	head_arc_feedforward(encoded_text, head_arc_representation);
//	print_shape(head_arc_representation);

	child_arc_feedforward(encoded_text, child_arc_representation);
//	print_shape(child_arc_representation);
//	print(head_arc_representation);
//	print(child_arc_representation);
	auto attended_arcs = arc_attention(head_arc_representation,
			child_arc_representation);

	head_tag_feedforward(encoded_text, head_tag_representation);
	child_tag_feedforward(encoded_text, child_tag_representation);

//	print(attended_arcs);
	if (predicted_heads.empty()) {
		predicted_heads.resize(seq_length + 1);
		predicted_heads = _mst_decode(head_tag_representation,
				child_tag_representation, attended_arcs, predicted_head_tags,
				predicted_heads);
	} else {
		predicted_heads.insert(predicted_heads.begin(), 0);
		predicted_heads = _structure_decode(head_tag_representation,
				child_tag_representation, attended_arcs, predicted_head_tags,
				predicted_heads);
	}

//	print(predicted_heads);
//	print(predicted_head_tags);
	predicted_heads.erase(predicted_heads.begin());
	predicted_head_tags.erase(predicted_head_tags.begin());

//	print(predicted_heads);
//	print(predicted_head_tags);

	return predicted_heads;
}

SyntaxParser::SyntaxParser(const string &modelFolder) :
		modelFolder(modelFolder),

		vocab(Text(modelFolder + "vocabulary/tokens.txt").read_vocab(1)),

		posTags(Text(modelFolder + "vocabulary/pos.txt").read_vocab(1)),

		depTags(Text(modelFolder + "vocabulary/head_tags.txt").readlines()),

		model(
				(BinaryFile&) (const BinaryFile&) BinaryFile(
						modelFolder + "model.h5")) {
	Timer timer(__PRETTY_FUNCTION__);
}

BiaffineDependencyParser::BiaffineDependencyParser(BinaryFile &dis) :
		_head_sentinel(read_tensor(dis)[0].row(0)),

		text_field_embedder(dis),

		encoder(dis),

		head_arc_feedforward(dis, Activator::elu),

		child_arc_feedforward(dis, Activator::elu),

		arc_attention(dis),

		head_tag_feedforward(dis, Activator::elu),

		child_tag_feedforward(dis, Activator::elu),

		tag_bilinear(dis),

		_pos_tag_embedding(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

SyntaxParser& SyntaxParser::instance_cn() {
//	Timer timer(__PRETTY_FUNCTION__);
//	auto folder = assetsDirectory() + "cn/parsers/biaffine/";
//	print(folder);
	static SyntaxParser instance(assetsDirectory() + "cn/parsers/biaffine/");

	return instance;
}

SyntaxParser& SyntaxParser::instance_en() {
	Timer timer(__PRETTY_FUNCTION__);
	static SyntaxParser instance(assetsDirectory() + "en/parsers/biaffine/");

	return instance;
}

SyntaxParser& SyntaxParser::instantiate() {
	auto &instance = SyntaxParser::instance_cn();

	instance = SyntaxParser(instance.modelFolder);

	return instance;
}

AugmentedLstm::AugmentedLstm(BinaryFile &dis) :
		input_linearity(read_matrix(dis).transpose()), state_linearity(dis,
				Activator::linear),

		hidden_size(input_linearity.cols() / 6) {
	Timer timer(__PRETTY_FUNCTION__);
}

StackedBidirectionalLstm::StackedBidirectionalLstm(BinaryFile &dis) :
		forward_layer_0(dis), backward_layer_0(dis),

		forward_layer_1(dis), backward_layer_1(dis),

		forward_layer_2(dis), backward_layer_2(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

Matrix& AugmentedLstm::operator ()(const Matrix &sequence_tensor,
		Matrix &output_accumulator) {
//	Timer timer(__PRETTY_FUNCTION__);
	int total_timesteps = sequence_tensor.rows();

//	cout << "total_timesteps = " << total_timesteps << endl;

	output_accumulator.resize(total_timesteps, hidden_size);
	Vector previous_memory, previous_state;

	previous_memory = previous_state = Vector::Zero(hidden_size);

	for (int index = 0; index < total_timesteps; ++index) {
		output_accumulator.row(index) = activate(sequence_tensor.row(index),
				previous_state, previous_memory);
	}

	return output_accumulator;
}

Vector& AugmentedLstm::activate(
		const Eigen::Block<const Matrix, 1, -1, 1> &timestep_input,
		Vector &previous_state, Vector &previous_memory) const {
//	cout << "hidden_size = " << hidden_size << endl;

//	print_shape(timestep_input);

	auto projected_input = timestep_input * input_linearity;
//	print(projected_input);
//	print_shape(projected_input);

//	print_shape(previous_state);

//	print_shape(state_linearity.weight);

	auto projected_state = state_linearity(previous_state);
//	print(projected_state);
	Vector input_gate = projected_input.leftCols(hidden_size)
			+ projected_state.leftCols(hidden_size);
	input_gate = sigmoid(input_gate);

//	print(input_gate);
	Vector forget_gate = projected_input.middleCols(hidden_size, hidden_size)
			+ projected_state.middleCols(hidden_size, hidden_size);
	forget_gate = sigmoid(forget_gate);
//	print(forget_gate);

	Vector memory_init = projected_input.middleCols(2 * hidden_size,
			hidden_size)
			+ projected_state.middleCols(2 * hidden_size, hidden_size);
	memory_init = tanh(memory_init);
//	print(memory_init);

	Vector output_gate = projected_input.middleCols(3 * hidden_size,
			hidden_size)
			+ projected_state.middleCols(3 * hidden_size, hidden_size);
	output_gate = sigmoid(output_gate);
//	print(output_gate);

	Vector memory = input_gate.cwiseProduct(memory_init)
			+ forget_gate.cwiseProduct(previous_memory);

	previous_memory = memory;
//error: memory is mutated after this operation! so save it before changing it!
	Vector timestep_output = output_gate.cwiseProduct(tanh(memory));
//	print(timestep_output);

	Vector highway_gate = projected_input.middleCols(4 * hidden_size,
			hidden_size)
			+ projected_state.middleCols(4 * hidden_size, hidden_size);
	highway_gate = sigmoid(highway_gate);

	Vector highway_input_projection = projected_input.rightCols(hidden_size);

	timestep_output = highway_gate.cwiseProduct(timestep_output)
			+ (Vector::Ones(highway_gate.cols()) - highway_gate).cwiseProduct(
					highway_input_projection);

	previous_state = timestep_output;

	return previous_state;

}

Matrix& AugmentedLstm::operator ()(const Matrix &sequence_tensor,
		Matrix &output_accumulator, bool go_forward) {
	if (go_forward)
		return (*this)(sequence_tensor, output_accumulator);

//	Timer timer(__PRETTY_FUNCTION__);
	int total_timesteps = sequence_tensor.rows();
	output_accumulator.resize(total_timesteps, hidden_size);

	Vector previous_memory, previous_state;
	previous_memory = previous_state = Vector::Zero(hidden_size);

	for (int index = total_timesteps - 1; index >= 0; --index) {
		output_accumulator.row(index) = activate(sequence_tensor.row(index),
				previous_state, previous_memory);
	}

	return output_accumulator;
}

Matrix& StackedBidirectionalLstm::operator ()(Matrix &output_sequence) {
//	Timer timer(__PRETTY_FUNCTION__);

	Matrix forward_output, backward_output;

	forward_layer_0(output_sequence, forward_output);
	backward_layer_0(output_sequence, backward_output, false);

//	print(forward_output);
//	print(backward_output);

	output_sequence.resize(output_sequence.rows(),
			forward_output.cols() + backward_output.cols());
	output_sequence << forward_output, backward_output;
//	print_shape(output_sequence);

	forward_layer_1(output_sequence, forward_output);
	backward_layer_1(output_sequence, backward_output, false);

	output_sequence.resize(output_sequence.rows(),
			forward_output.cols() + backward_output.cols());
	output_sequence << forward_output, backward_output;

//	print_shape(output_sequence);

	forward_layer_2(output_sequence, forward_output);
	backward_layer_2(output_sequence, backward_output, false);

	output_sequence.resize(output_sequence.rows(),
			forward_output.cols() + backward_output.cols());
	output_sequence << forward_output, backward_output;

//	print_shape(output_sequence);

	return output_sequence;
}

Tensor BiaffineDependencyParser::energy(const Matrix &head_tag,
		const Matrix &child_tag, Matrix &attended_arcs) {
//	print(head_tag);
//	print(child_tag);
//	print_shape(head_tag);
//	print_shape(child_tag);
//	print_shape(attended_arcs);
//	Timer timer(__PRETTY_FUNCTION__);

	int sequence_length = head_tag.rows();
	Tensor head_tag_representation(sequence_length);
	for (int i = 0; i < sequence_length; ++i) {
		head_tag_representation[i] = broadcast(head_tag.row(i),
				sequence_length);
	}

	Tensor child_tag_representation(sequence_length);
	for (int i = 0; i < sequence_length; ++i) {
		child_tag_representation[i] = child_tag;
	}

//	print(head_tag_representation);
//	print(child_tag_representation);
	auto pairwise_head_logits = tag_bilinear(head_tag_representation,
			child_tag_representation);

	pairwise_head_logits = transpose<2, 0, 1>(
			log_softmax(pairwise_head_logits));
//	pairwise_head_logits = transpose_201(log_softmax(pairwise_head_logits));

//	print_tensor(pairwise_head_logits);

//	print_shape(attended_arcs);
	log_softmax(attended_arcs).transposeInPlace();
//	print(predicted_head_tags);
//	print(pairwise_head_logits);
//	print(attended_arcs);

	return exp(pairwise_head_logits += attended_arcs);
}

VectorI &BiaffineDependencyParser::_mst_decode(const Matrix &head_tag,
		const Matrix &child_tag, Matrix &attended_arcs,
		VectorI &predicted_head_tags, VectorI &predicted_head_indices) {
	return _run_mst_decoding(energy(head_tag, child_tag, attended_arcs),
			predicted_head_tags, predicted_head_indices);
}

VectorI& BiaffineDependencyParser::_structure_decode(const Matrix &head_tag,
		const Matrix &child_tag, Matrix &attended_arcs,
		VectorI &instance_head_tags, VectorI &instance_heads) {
	Timer timer(__PRETTY_FUNCTION__);

	auto energy = this->energy(head_tag, child_tag, attended_arcs);

	MatrixI tag_ids = argmax(energy, 0);

	int seq_length = instance_heads.size();
	instance_head_tags.resize(seq_length);
//	# Find the labels which correspond to the edges in the max spanning tree.
	for (int child = 0; child < seq_length; ++child) {
		int parent = instance_heads[child];
		instance_head_tags[child] = tag_ids[parent][child];
	}

//	# We don't care what the head or tag is for the root token, but by default it's;
//	# not necesarily the same in the bat;ched vs unbatched case, which is annoying.;
//	# Here we'll just set them to zero.;
	instance_heads[0] = 0;
	instance_head_tags[0] = 0;

	return instance_heads;
}

#include "chu_liu_edmonds.h"

VectorI &BiaffineDependencyParser::_run_mst_decoding(const Tensor &energy,
		VectorI &instance_head_tags, VectorI &instance_heads) {
//	Timer timer(__PRETTY_FUNCTION__);
	Matrix scores;
	MatrixI tag_ids = argmax(energy, scores, 0);

//    # Decode the heads. Because we modify the scores to prevent
//    # adding in word -> ROOT edges, we need to find the labels ourselves.
	::_run_mst_decoding(scores, instance_heads);

//    # Find the labels which correspond to the edges in the max spanning tree.
	int seq_length = instance_heads.size();
	instance_head_tags.resize(seq_length);
//	print(instance_head_tags);

	for (int child = 0; child < seq_length; ++child) {
		int parent = instance_heads[child];
		if (parent < 0)
			instance_head_tags[child] = 0;
		else
			instance_head_tags[child] = tag_ids[parent][child];
	}

	instance_head_tags[0] = 0;
//	print(instance_head_tags);
	return instance_heads;
}
void SyntaxParser::test_cn() {
	auto &syntaxParser = instance_cn();
//这比山还高比海还深的情谊,我们怎么能忘怀?
	vector<std::string> _seg = { "你", "说", ",", "这", "比", "山", "还", "高", "比",
			"海", "还", "深", "的", "情谊", ",", "我们", "怎么", "能", "忘怀", "?", "仿写",
			"句子" };
	vector<std::string> _pos = { "PN", "VT", "PU", "DT", "P", "NN", "AD", "VA",
			"P", "NN", "AD", "VA", "DE", "NN", "PU", "PN", "AD", "MD", "VT",
			"PU", "VT", "NN" };

	vector<String> seg = std::toStrings(_seg);
	vector<String> pos = std::toStrings(_pos);
	vector<String> dep;
	auto heads = syntaxParser(seg, pos, dep);
	cout << "seg = " << seg << endl;
	cout << "pos = " << pos << endl;
	cout << "dep = " << dep << endl;
	cout << "heads = " << heads << endl;
}

