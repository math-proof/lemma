#pragma once
#include "../utility.h"
#include "../layers.h"

struct NERTagger {
	using object = ::object<NERTagger> ;

	dict<char16_t, int> word2id;
	Embedding embedding, repertoire_embedding;

	BidirectionalLSTM lstm;

	Conv1D<Padding::valid> con1D0, con1D1, con1D2;

	CRF wCRF;

	VectorI& predict(const VectorI &predict_text, VectorI &repertoire_code);

	TensorD& _predict(const String &predict_text,
			VectorI&repertoire_code, TensorD &arr);

	NERTagger(BinaryFile &dis);
};

struct NERTaggerDict {

	static ::dict<string, NERTagger::object> dict;

	static NERTagger::object& getTagger(const string &service);

	static vector<int> get_repertoire_code(const string &service,
			const String &text);

	static VectorI& predict(const string &service, const String &text,
			VectorI&);
	static TensorD& _predict(const string &service,
			const String &text, VectorI&, TensorD&);
};
