#include "../../../std/utility.h"
#include "./chunking.h"
/*
vector<Tensor> SyntacticChunkingTagger::operator()(
		const vector<vector<String>> &texts, bool) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	int size = texts.size();

	vector<Tensor> outputs(size);

	Tensor a_K, a_V;
	for (int i = 0; i < size; ++i) {
		auto &text = texts[i];
		if (text.size()) {
			Tensor _a_K, _a_V;
			outputs[i] = (*this)(text, _a_K, _a_V, true);
			if (_a_K.size() > a_K.size()) {
				a_K = _a_K;
				a_V = _a_V;
			}
		}
	}
	outputs.push_back(a_K);
	outputs.push_back(a_V);
//	outputs.insert(outputs.begin(), { a_K, a_V });
//	outputs.resize(2);
	return outputs;
}
*/

MatrixI SyntacticChunkingTagger::operator()(
		const vector<vector<String>> &texts) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	int size = texts.size();
	MatrixI chunks(size);

	for (int i = 0; i < size; ++i) {
		auto &text = texts[i];
		if (text.size())
			chunks[i] = (*this)(text);
	}

	return chunks;
}

MatrixI SyntacticChunkingTagger::operator()(const vector<vector<String>> &texts,
		bool parallel) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	int size = texts.size();
	MatrixI chunks(size);

#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		auto &text = texts[i];
		if (text.size())
			chunks[i] = (*this)(text);
	}

	return chunks;
}

MatrixI& SyntacticChunkingTagger::operator()(MatrixI &texts) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(texts);

	int size = texts.size();
#pragma omp parallel for
	for (int i = 0; i < size; ++i) {
		auto &text = texts[i];
		if (text.size())
			texts[i] = (*this)(text);
	}

	return texts;
}

VectorI SyntacticChunkingTagger::operator()(const vector<String> &texts) {
//	Timer timer(__PRETTY_FUNCTION__);
	auto input_ids = string2id(texts, word2id);
	return (*this)(input_ids);
}

Tensor SyntacticChunkingTagger::operator()(const vector<String> &texts,
		Tensor &a_K, Tensor &a_V, bool) {
//	Timer timer(__PRETTY_FUNCTION__);

	auto input_ids = string2id(texts, word2id);
	print(input_ids);
	return (*this)(input_ids, a_K, a_V, true);
}

VectorI& SyntacticChunkingTagger::operator()(VectorI &input_ids) {
//	Timer timer(__PRETTY_FUNCTION__);

	auto embedding_output = wordEmbedding(input_ids);

	auto a_K = this->a_K_embedding(input_ids.size(), k_max);
//	print(a_K);
	auto a_V = this->a_V_embedding(input_ids.size(), k_max);
//	print(a_V);

//	auto cnn_layer = conv1D2(conv1D1(conv1D0(embedding_output)));
//	auto cnn_layer = conv1D1(conv1D0(embedding_output));
	auto cnn_layer = conv1D0(embedding_output);

	auto &transformed = transformer(cnn_layer, a_K, a_V, k_max);

	auto &norm_layer = layerNormalization(transformed);

	return wCRF(norm_layer, input_ids);
}

Tensor SyntacticChunkingTagger::operator()(VectorI &input_ids, Tensor &a_K,
		Tensor &a_V, bool) {
	Tensor outputs;

	auto embedding_output = wordEmbedding(input_ids);
	outputs.push_back(embedding_output);

//	auto cnn_layer = conv1D2(conv1D1(conv1D0(embedding_output)));
//	auto cnn_layer = conv1D1(conv1D0(embedding_output));
	auto cnn_layer = conv1D0(embedding_output);
	a_K = this->a_K_embedding(input_ids.size(), k_max);
	a_V = this->a_V_embedding(input_ids.size(), k_max);
//	print(a_K[0]);
//	print(a_K_embedding.embeddings);
//	print(a_V);
	outputs.push_back(cnn_layer);

//	auto &transformed = transformer(cnn_layer, a_K, a_V, true);
	auto &transformed = transformer(cnn_layer, a_K, a_V, k_max);
	outputs.push_back(transformed);
//	addAll(outputs, transformed);

	auto &norm_layer = layerNormalization(transformed);
	outputs.push_back(norm_layer);

	auto crf_layer = wCRF(norm_layer, input_ids);
	print(crf_layer);

	return outputs;
}

SyntacticChunkingTagger::SyntacticChunkingTagger(const string &modelPath,
		const string &vocabFilePath) :
		SyntacticChunkingTagger(
				(BinaryFile&) (const BinaryFile&) BinaryFile(modelPath),
				vocabFilePath) {
	Timer timer(__PRETTY_FUNCTION__);
}

SyntacticChunkingTagger::SyntacticChunkingTagger(BinaryFile &dis,
		const string &vocabFilePath) :
		word2id(Text(vocabFilePath).read_vocab()),

		wordEmbedding(dis),

		conv1D0(dis), //conv1D1(dis), //conv1D2(dis),

		a_K_embedding(dis), a_V_embedding(dis),

		transformer(dis, 1/*num_hidden_layers*/, 8/*num_attention_heads*/, {
				Activator::relu }),

		layerNormalization(dis),

		wCRF(dis) {
	Timer timer(__PRETTY_FUNCTION__);
}

extern string workingDirectory;
SyntacticChunkingTagger& SyntacticChunkingTagger::instance_en() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/en/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/en/parsers/claim/chunking/vocab.txt");
	return inst;
}

SyntacticChunkingTagger& SyntacticChunkingTagger::instance_cn() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/cn/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/cn/parsers/claim/chunking/vocab.txt");
	return inst;
}

SyntacticChunkingTagger& SyntacticChunkingTagger::instance_tw() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/tw/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/tw/parsers/claim/chunking/vocab.txt");
	return inst;
}

SyntacticChunkingTagger& SyntacticChunkingTagger::instance_jp() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/jp/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/jp/parsers/claim/chunking/vocab.txt");
	return inst;
}

SyntacticChunkingTagger& SyntacticChunkingTagger::instance_kr() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/kr/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/kr/parsers/claim/chunking/vocab.txt");
	return inst;
}

SyntacticChunkingTagger& SyntacticChunkingTagger::instance_de() {
//	Timer timer(__PRETTY_FUNCTION__);
	static SyntacticChunkingTagger inst(
			workingDirectory + "assets/de/parsers/claim/chunking/model.bin",
			workingDirectory + "assets/de/parsers/claim/chunking/vocab.txt");
	return inst;
}

void SyntacticChunkingTagger::test_cn() {
	vector<std::string> claim_text = { "1", ".", "一种", "电磁换向阀", "，", "包括", "阀体",
			"(", "1", ")", "、", "阀芯", "(", "2", ")", "、", "阀体", "端盖", "(", "3",
			")", "和", "电磁铁", "组件", "(", "4", ")", "；", "\\n", "所述", "阀体", "(",
			"1", ")", "包括", "第一", "油口", "(", "1", "-", "4", ")", "、", "第二",
			"油口", "(", "1", "-", "5", ")", "、", "回油口", "(", "1", "-", "6", ")",
			"、", "进油口", "(", "1", "-", "7", ")", "和", "沿", "其", "轴向", "设有", "的",
			"阀体", "主孔", "(", "1", "-", "8", ")", "，", "以及", "沿", "阀体", "主孔",
			"(", "1", "-", "8", ")", "内壁", "上", "轴向", "分开", "布置", "的", "第一",
			"油道", "(", "1", "-", "1", ")", "、", "第二", "油道", "(", "1", "-", "2",
			")", "和", "第三", "油道", "(", "1", "-", "3", ")", "，", "所述", "第一",
			"油口", "(", "1", "-", "4", ")", "与", "第一", "油道", "(", "1", "-", "1",
			")", "相连通", "，", "第二", "油口", "(", "1", "-", "5", ")", "与", "第三",
			"油道", "(", "1", "-", "3", ")", "相连通", "，", "进油口", "(", "1", "-",
			"7", ")", "与", "第二", "油道", "(", "1", "-", "2", ")", "相连通", "，",
			"所述", "第一", "油道", "(", "1", "-", "1", ")", "、", "第二", "油道", "(",
			"1", "-", "2", ")", "和", "第三", "油道", "(", "1", "-", "3", ")", "均",
			"与", "阀体", "主孔", "(", "1", "-", "8", ")", "相连通", "；", "\\n", "所述",
			"阀体", "(", "1", ")", "内设有", "回油", "流道", "(", "1", "-", "9", ")",
			"，", "所述", "回油口", "(", "1", "-", "6", ")", "与", "回油", "流道", "(",
			"1", "-", "9", ")", "相连通", "，", "回油", "流道", "(", "1", "-", "9", ")",
			"的", "两端", "分别", "位于", "第一", "油道", "(", "1", "-", "1", ")", "和",
			"第三", "油道", "(", "1", "-", "3", ")", "的", "外侧", "，", "且", "回油",
			"流道", "(", "1", "-", "9", ")", "的", "两端", "与", "阀体", "主孔", "(", "1",
			"-", "8", ")", "相连通", "；", "\\n", "所述", "阀体", "(", "1", ")", "的",
			"一端", "与", "电磁铁", "组件", "(", "4", ")", "固定", "连接", ",", "阀体", "端盖",
			"(", "3", ")", "与", "阀体", "(", "1", ")", "的", "另一端", "密封", "连接",
			"；", "\\n", "所述", "阀体", "主孔", "(", "1", "-", "8", ")", "内", "位于",
			"回油", "流道", "(", "1", "-", "9", ")", "的", "两端", "之间", "，", "还有",
			"沿", "轴向", "分开", "布置", "的", "阀体", "第一", "台阶", "(", "1", "-", "11",
			")", "、", "阀体", "第二", "台阶", "(", "1", "-", "12", ")", "、", "阀体",
			"第三", "台阶", "(", "1", "-", "13", ")", "和", "阀体", "第四", "台阶", "(",
			"1", "-", "14", ")", "；", "\\n", "所述", "阀芯", "(", "2", ")", "设在",
			"阀体", "(", "1", ")", "的", "阀体", "主孔", "(", "1", "-", "8", ")", "内",
			"，", "阀芯", "(", "2", ")", "的", "中部", "具有", "沿", "轴向", "分开", "布置",
			"的", "阀芯", "第一", "凸台", "(", "2", "-", "1", ")", "和", "阀芯", "第二凸",
			"台", "(", "2", "-", "2", ")", "，", "且", "阀芯", "第一", "凸台", "(", "2",
			"-", "1", ")", "和", "阀芯", "第二凸", "台", "(", "2", "-", "2", ")", "上",
			"均", "设有", "通", "油面", "(", "2", "-", "6", ")", "；", "\\n", "所述",
			"电磁铁", "组件", "(", "4", ")", "包括", "第一", "铁芯", "(", "4", "-", "1",
			")", "、", "第二", "铁芯", "(", "4", "-", "2", ")", "、", "衔铁", "(", "4",
			"-", "3", ")", "、", "推拉杆", "(", "4", "-", "3", "-", "2", ")", "、",
			"线圈", "(", "4", "-", "4", ")", "、", "复位弹簧", "(", "4", "-", "5", ")",
			"、", "磁轭", "(", "4", "-", "6", ")", "、", "隔磁", "套", "(", "7", ")",
			"和", "导磁环", "(", "8", ")", "，", "所述", "衔铁", "(", "4", "-", "3", ")",
			"的", "一端", "与", "推拉杆", "(", "4", "-", "3", "-", "2", ")", "的", "一端",
			"装", "连", "或", "制成", "一体", "，", "所述", "隔磁", "套", "(", "7", ")", "的",
			"两端", "分别", "装", "连", "或", "焊接", "在", "第一", "铁芯", "(", "4", "-",
			"1", ")", "和", "第二", "铁芯", "(", "4", "-", "2", ")", "上", "，", "且",
			"隔磁", "套", "(", "7", ")", "位于", "衔铁", "(", "4", "-", "3", ")", "的",
			"外周", "，", "所述", "线圈", "(", "4", "-", "4", ")", "设在", "隔磁", "套",
			"(", "7", ")", "的", "外周", "，", "且", "两个", "线圈", "(", "4", "-", "4",
			")", "之间", "装有", "导磁环", "(", "8", ")", "，", "所述", "磁轭", "(", "4",
			"-", "6", ")", "设在", "两个", "线圈", "(", "4", "-", "4", ")", "的", "外周",
			"；", "\\n", "所述", "第一", "铁芯", "(", "4", "-", "1", ")", "设有", "轴向",
			"的", "台阶孔", "(", "4", "-", "1", "-", "1", ")", "，", "且", "台阶孔", "(",
			"4", "-", "1", "-", "1", ")", "内设有", "垫片", "(", "5", ")", "，", "所述",
			"推拉杆", "(", "4", "-", "3", "-", "2", ")", "上", "具有", "限位", "凸起",
			"(", "4", "-", "3", "-", "1", ")", "，", "限位", "凸起", "(", "4", "-",
			"3", "-", "1", ")", "抵", "在", "垫片", "(", "5", ")", "的", "一侧", "，",
			"推拉杆", "(", "4", "-", "3", "-", "2", ")", "的", "另一端", "穿过", "垫片",
			"(", "5", ")", "并", "与", "阀芯", "(", "2", ")", "的", "一端", "固定", "连接",
			"，", "所述", "阀芯", "(", "2", ")", "的", "一端", "套装", "有", "弹簧座", "(",
			"6", ")", "，", "推拉杆", "(", "4", "-", "3", "-", "2", ")", "的", "另一端",
			"的", "外周", "套装", "有", "复位弹簧", "(", "4", "-", "5", ")", "，", "且",
			"复位弹簧", "(", "4", "-", "5", ")", "的", "一端", "与", "弹簧座", "(", "6",
			")", "的", "一侧", "相抵", "，", "所述", "复位弹簧", "(", "4", "-", "5", ")",
			"的", "另一端", "与", "垫片", "(", "5", ")", "的", "另一侧", "相抵", "；", "其",
			"特征", "在于", "：", "\\n", "a", "、", "所述", "阀芯", "(", "2", ")", "的",
			"两端", "还", "分别", "具有", "阀芯", "笫", "三", "凸台", "(", "2", "-", "3",
			")", "和", "阀芯", "第四", "凸台", "(", "2", "-", "4", ")", "；", "\\n",
			"b", "、", "所述", "阀体", "(", "1", ")", "内", "还", "设有", "油压", "平衡",
			"流道", "(", "1", "-", "10", ")", "，", "所述", "油压", "平衡", "流道", "(",
			"1", "-", "10", ")", "的", "两端", "分别", "位于", "回油", "流道", "(", "1",
			"-", "9", ")", "两端", "的", "外侧", "，", "且", "油压", "平衡", "流道", "(",
			"1", "-", "10", ")", "的", "两端", "与", "阀体", "主孔", "(", "1", "-", "8",
			")", "相连通", "，", "阀体", "(", "1", ")", "内", "阀体", "主孔", "(", "1",
			"-", "8", ")", "的", "两端", "还", "沿", "轴向", "分别", "设有", "阀体", "第五",
			"台阶", "(", "1", "-", "15", ")", "和", "阀体", "第六", "台阶", "(", "1",
			"-", "16", ")", "，", "阀体", "第五", "台阶", "(", "1", "-", "15", ")",
			"和", "阀体", "第六", "台阶", "(", "1", "-", "16", ")", "分别", "位于", "回油",
			"流道", "(", "1", "-", "9", ")", "两端", "的", "外侧", "和", "油压", "平衡",
			"流道", "(", "1", "-", "10", ")", "两端", "的", "内侧", "；", "\\n", "c",
			"、", "所述", "阀芯", "(", "2", ")", "两端", "的", "阀芯", "笫", "三", "凸台",
			"(", "2", "-", "3", ")", "和", "阀芯", "第四", "凸台", "(", "2", "-", "4",
			")", "分别", "与", "相应", "的", "阀体", "第五", "台阶", "(", "1", "-", "15",
			")", "和", "阀体", "第六", "台阶", "(", "1", "-", "16", ")", "滑动", "配合",
			"；", "\\n", "d", "、", "所述", "弹簧座", "(", "6", ")", "的", "另一侧", "能",
			"与", "阀体", "第六", "台阶", "(", "1", "-", "16", ")", "和", "/", "或",
			"阀芯", "第四", "凸台", "(", "2", "-", "4", ")", "相抵", "。", "\\n" };

//	claim_text.resize(129);
	claim_text.resize(100);
	Tensor tmp;
	print(instance_cn()(std::toStrings(claim_text), tmp, tmp, true));
	cout << "test successfully" << endl;
}

void SyntacticChunkingTagger::test_en() {
	vector<string> claim_text = { "claims", "1", ".", "~", "a", "portable",
			"computer", "comprising", ":", "movement", "detection", "means",
			"responsive", "to", "movement", "of", "the", "computer", "to",
			"produce", "an", "electrical", "output", "signal", "representative",
			"of", "such", "movement", ",", "a", "storage", "medium", "for",
			"storing", "data", "defining", "a", "multiplicity", "of",
			"displayable", "pages", "each", "comprising", "of", "a",
			"plurality", "of", "lines", ";", "a", "display", "having", "a",
			"corresponding", "plurality", "of", "lines", "to", "enable", "one",
			"of", "the", "multiplicity", "of", "pages", "to", "be", "displayed",
			";", "and", "processing", "means", "responsive", "to", "the",
			"output", "of", "said", "movement", "detection", "means", "to",
			"determine", "detected", "movement", "data", "defining", "a",
			"user", "'", "s", "intention", ",", "the", "processing", "means",
			"using", "said", "movement", "data", "to", "provide", "a", "mode",
			"response", "selected", "from", "a", "multiplicity", "of", "stored",
			"possible", "modes", ",", "wherein", "detected", "movement", "data",
			"is", "used", "to", "effect", "scrolling", "of", "displayed",
			"information", "such", "that", "portions", "of", "data", "defining",
			"alphanumeric", "or", "graphic", "information", "outside", "a",
			"currently", "displayed", "screen", "may", "be", "selected", "by",
			"the", "user", ",", "the", "scrolling", "of", "displayed",
			"information", "effectively", "displaying", "a", "part", "of", "an",
			"adjacent", "screen", ".", "\\n", "2", ".", "~", "a", "portable",
			"computer", "comprising", ":", "movement", "detection", "means",
			"responsive", "to", "movement", "of", "the", "computer", "to",
			"produce", "an", "electrical", "output", "signal", "representative",
			"of", "such", "movement", ",", "a", "storage", "medium", "for",
			"storing", "data", "defining", "a", "multiplicity", "of",
			"displayable", "pages", "each", "comprising", "of", "a",
			"plurality", "of", "lines", ";", "a", "display", "having", "a",
			"corresponding", "plurality", "of", "lines", "to", "enable", "one",
			"of", "the", "multiplicity", "of", "pages", "to", "be", "displayed",
			";", "and", "processing", "means", "responsive", "to", "the",
			"output", "of", "said", "movement", "detection", "means", "to",
			"determine", "detected", "movement", "data", "defining", "a",
			"user", "'", "s", "intention", ",", "the", "processing", "means",
			"using", "said", "movement", "data", "to", "provide", "a", "mode",
			"response", "selected", "from", "a", "multiplicity", "of", "stored",
			"possible", "modes", ",", "in", "which", "a", "relative", "lateral",
			"tilting", "movement", "causes", "the", "display", "of",
			"information", "stored", "as", "to", "one", "or", "other", "side",
			"of", "currently", "displayed", "information", ".", "\\n", "3", ".",
			"~", "a", "portable", "computer", "comprising", ":", "movement",
			"detection", "means", "responsive", "to", "movement", "of", "the",
			"computer", "to", "produce", "an", "electrical", "output", "signal",
			"representative", "of", "such", "movement", ",", "a", "storage",
			"medium", "for", "storing", "data", "defining", "a", "multiplicity",
			"of", "displayable", "pages", "each", "comprising", "of", "a",
			"plurality", "of", "lines", ";", "a", "display", "having", "a",
			"corresponding", "plurality", "of", "lines", "to", "enable", "one",
			"of", "the", "multiplicity", "of", "pages", "to", "be", "displayed",
			";", "and", "processing", "means", "responsive", "to", "the",
			"output", "of", "said", "movement", "detection", "means", "to",
			"determine", "detected", "movement", "data", "defining", "a",
			"user", "'", "s", "intention", ",", "the", "processing", "means",
			"using", "said", "movement", "data", "to", "provide", "a", "mode",
			"response", "selected", "from", "a", "multiplicity", "of", "stored",
			"possible", "modes", ",", "in", "which", "relative", "rolling",
			"movement", "causes", "the", "display", "of", "information",
			"stored", "as", "above", "or", "below", "currently", "displayed",
			"information", ".", "\\n", "4", ".", "~", "a", "portable",
			"computer", "comprising", ":", "movement", "detection", "means",
			"responsive", "to", "movement", "of", "the", "computer", "to",
			"produce", "an", "electrical", "output", "signal", "representative",
			"of", "such", "movement", ",", "processing", "means", "responsive",
			"to", "the", "output", "of", "said", "movement", "detection",
			"means", "to", "determine", "detected", "movement", "data",
			"defining", "a", "user", "'", "s", "intention", ",", "the",
			"processing", "means", "using", "said", "data", "to", "provide",
			"a", "mode", "response", "selected", "from", "a", "multiplicity",
			"of", "stored", "possible", "modes", ";", "and", "wherein", "the",
			"processing", "means", "is", "responsive", "to", "detected",
			"movement", "data", "to", "determine", "a", "most", "likely",
			"orientation", "of", "the", "computer", "display", "means", ",",
			"the", "processing", "means", "causing", "the", "displayed",
			"information", "to", "be", "oriented", "accordingly", ".", "\\n",
			"5", ".", "~", "a", "portable", "computer", "as", "in", "claim",
			"4", ",", "in", "which", "a", "plurality", "of", "switch", "means",
			"responsive", "to", "user", "action", "is", "included", "adjacent",
			"to", "the", "display", "means", ",", "the", "respective",
			"function", "of", "each", "of", "the", "switch", "means", "being",
			"oriented", "to", "match", "the", "orientation", "of", "displayed",
			"information", ".", "\\n", "6", ".", "~", "a", "portable",
			"computer", "as", "in", "claim", "4", "further", "comprising", "a",
			"touch", "sensitive", "static", "potentiometer", "strip",
			"responsive", "to", "movement", "of", "a", "user", "'", "s",
			"finger", "to", "simulate", "movement", "of", "a", "potentiometer",
			",", "the", "orientation", "of", "said", "potentiometer",
			"reflecting", "the", "orientation", "of", "the", "displayed",
			"information", ".", "\\n", "7", ".", "~", "a", "portable",
			"computer", "comprising", ":", "movement", "detection", "means",
			"responsive", "to", "movement", "of", "the", "computer", "to",
			"produce", "an", "electrical", "output", "signal", "representative",
			"of", "such", "movement", ",", "processing", "means", "responsive",
			"to", "the", "output", "of", "said", "movement", "detection",
			"means", "to", "determine", "detected", "movement", "data",
			"defining", "a", "user", "'", "s", "intention", ",", "the",
			"processing", "means", "using", "said", "data", "to", "provide",
			"a", "mode", "response", "selected", "from", "a", "multiplicity",
			"of", "stored", "possible", "modes", ";", "and", "wherein",
			"proximity", "detection", "means", "which", "provides", "signals",
			"indicative", "of", "the", "proximity", "of", "the", "computer",
			"display", "screen", "to", "a", "user", "'", "s", "view", ",",
			"the", "processing", "means", "being", "further", "responsive",
			"to", "changes", "in", "relative", "proximity", "to", "increase",
			"or", "decrease", "the", "density", "of", "displayed",
			"information", ".", "\\n", "8", ".", "~", "a", "portable",
			"computer", "as", "in", "any", "one", "of", "claims", "1", "to",
			"3", ",", "in", "which", "the", "processing", "means", "stores",
			"data", "defining", "an", "authorised", "user", "'", "s",
			"password", ",", "the", "processing", "means", "being", "locked",
			"in", "a", "secure", "mode", "until", "detected", "movement",
			"data", "corresponding", "to", "the", "security", "data", "is",
			"received", ".", "\\n", "9", ".", "~", "a", "portable", "computer",
			"as", "to", "any", "one", "of", "claims", "1", "to", "3", ",",
			"further", "comprising", "a", "sound", "input", "device", ",",
			"the", "processing", "means", "being", "responsive", "to", "voice",
			"input", "signals", "from", "a", "user", "to", "derive",
			"alphanumeric", "data", ".", "\\n", "10", ".", "~", "a", "portable",
			"computer", "as", "in", "any", "one", "of", "claims", "1", "to",
			"3", ",", "including", "a", "sound", "output", "device", ",", "the",
			"processing", "means", "being", "arranged", "to", "provide",
			"output", "of", "speech", "or", "other", "sound", "signals",
			"derived", "from", "stored", "data", ".", "\\n", "11", ".", "~",
			"a", "portable", "computer", "as", "in", "claim", "9", ",",
			"further", "including", "a", "sound", "output", "device", "in",
			"combination", "with", "a", "radio", "transceiver", "whereby",
			"cellular", "or", "radio", "telephony", "networks", "may", "be",
			"used", ".", "\\n", "12", ".", "~", "a", "portable", "computer",
			"as", "in", "any", "one", "of", "claims", "1", "to", "3", ",",
			"including", "radio", "transmission", "or", "infrared",
			"transmission", "means", ",", "the", "processing", "means", "being",
			"responsive", "to", "detected", "movement", "data", "to", "output",
			"to", "the", "transmission", "means", "signals", "representative",
			"of", "the", "detected", "movement", ".", "\\n", "13", ".", "~",
			"a", "portable", "computer", "as", "in", "any", "one", "of",
			"claims", "1", "to", "3", ",", "including", "radio", "transmission",
			"or", "infrared", "transmission", "means", ",", "the", "processing",
			"means", "being", "responsive", "to", "detected", "movement",
			"data", "to", "output", "to", "the", "transmission", "means",
			"signals", "representative", "of", "alphanumeric", "characters",
			".", "\\n", "14", ".", "~", "a", "portable", "computer", "as", "in",
			"any", "one", "of", "claims", "1", "to", "3", ",", "including",
			"radio", "transceiver", "means", ",", "the", "processing", "means",
			"being", "responsive", "to", "detected", "movement", "data",
			"which", "identifies", "another", "device", "to", "cause", "the",
			"transmission", "of", "coded", "signals", "including", "a",
			"message", "for", "display", ".", "\\n", "15", ".", "~", "a",
			"portable", "computer", "as", "in", "claim", "14", "in", "which",
			"the", "processing", "means", "is", "responsive", "to", "received",
			"encoded", "radio", "signals", "to", "activate", "a", "paging",
			"alert", ".", "\\n", "16", ".", "~", "a", "portable", "computer",
			"as", "in", "claim", "15", ",", "in", "which", "the", "page",
			"alert", "comprises", "a", "tone", ".", "\\n", "17", ".", "~", "a",
			"portable", "computer", "as", "in", "claim", "14", ",", "in",
			"which", "the", "paging", "alert", "comprises", "an", "operation",
			"of", "a", "vibrating", "means", ".", "\\n", "18", ".", "~", "a",
			"portable", "computer", "as", "in", "claim", "14", ",", "in",
			"which", "the", "processing", "means", "causes", "the", "display",
			"of", "a", "message", "derived", "from", "the", "information",
			"received", ".", "\\n", "19", ".", "~", "a", "portable", "computer",
			"as", "in", "any", "one", "of", "claims", "1", "to", "3", ",",
			"housed", "in", "a", "casing", "shaped", "to", "facilitate", "a",
			"user", "holding", "the", "computer", "as", "a", "writing",
			"stylus", ".", "\\n", "20", ".", "~", "a", "portable", "computer",
			"as", "in", "claim", "19", ",", "in", "which", "the", "casing",
			"comprises", "a", "radiused", "triangular", "cross", "-", "section",
			"along", "a", "substantial", "portion", "of", "its", "length", ".",
			"~", "\\n", "21", ".", "~", "a", "portable", "computer", "as", "in",
			"claim", "20", ",", "in", "which", "the", "casing", "includes", "a",
			"flattened", "section", "incorporating", "a", "display", "screen",
			".", "\\n", "22", ".", "~", "a", "portable", "computer", "as", "in",
			"any", "one", "of", "claims", "1", "to", "3", ",", "wherein", "the",
			"processing", "means", "is", "responsive", "to", "detected",
			"movement", "data", "to", "determine", "a", "most", "likely",
			"orientation", "of", "the", "computer", "display", "means", ",",
			"the", "processing", "means", "causing", "the", "displayed",
			"information", "to", "be", "oriented", "accordingly", ".", "\\n",
			"23", ".", "~", "a", "portable", "computer", "as", "in", "any",
			"one", "of", "claims", "1", "to", "3", ",", "in", "which", "a",
			"plurality", "of", "switch", "means", "responsive", "to", "user",
			"action", "is", "included", "adjacent", "to", "the", "display",
			"means", ",", "the", "respective", "function", "of", "each", "of",
			"the", "switch", "means", "being", "oriented", "to", "match", "the",
			"orientation", "of", "displayed", "information", "." };

	print(SyntacticChunkingTagger::instance_en()(std::toStrings(claim_text)));
}

extern "C" {
MatrixI keras_parsers_claim_chunking_cn(MatrixI &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	strip_tailing_zeros(text);

	return numpify(SyntacticChunkingTagger::instance_cn()(text));
}

MatrixI keras_parsers_claim_chunking_en(MatrixI &text) {
//	Timer timer(__PRETTY_FUNCTION__);
	strip_tailing_zeros(text);
	return numpify(SyntacticChunkingTagger::instance_en()(text));
}

VectorI keras_parsers_claim_chunking_cn_single(const vector<String> &text) {
	Timer timer(__PRETTY_FUNCTION__);
	print(text);
	return SyntacticChunkingTagger::instance_cn()(text);
}
}
