class CounterPart{
    constructor(parent, kwargs) {
        this.parent = parent;
		Object.assign(this, kwargs);
    }

	get that() {
		return this.parent;
	}

	get relation() {
		return this.parent._relation;
	}

	get lengths() {
		return this.parent._lengths;
	}

	get inputs() {
		return this.parent._inputs;
	}

	get confidence(){
		return this.parent._confidence;
	}

	get header(){
		return this.parent._header;
	}

	set header(header){
		this.parent._header = header;
	}

	get phrase(){
		return this.parent._phrase;
	}

	set phrase(phrase){
		this.parent._phrase = phrase;
	}

	get column(){
		return this.parent._column;
	}

	set column(column){
		this.parent._column = column;
	}

	get confidence_pair(){
		return this.parent._confidence_pair;
	}

	get textContent(){
		return this.parent._textContent;
	}

	get textContentOf(){
		return this.parent._textContentOf;
	}

	get index2codon(){
		return this.parent._index2codon;
	}

	get codonCell(){
		return this.parent._codonCell;
	}

	get initialize_vocab() {
		return this.parent._initialize_vocab;
	}

	get async_render(){
		return this.parent._async_render;
	}

	get render(){
		return this.parent._render;
	}

	get get_indices(){
		return this.parent._get_indices;
	}

	get seq_to_range(){
		return this.parent._seq_to_range;
	}

	get codon_to_range(){
		return this.parent._codon_to_range;
	}

	get true_positive_per_entity(){
		return this.parent.true_positive_per_entity;
	}

	get entity_linking_from_that_to_this() {
		return this.parent.entity_linking_from_this_to_that;
	}

	get entity_linking_from_this_to_that() {
		return this.parent.entity_linking_from_that_to_this;
	}

	get get_id_indices(){
		return this.parent._get_id_indices;
	}

	get textSelected(){
		return this.parent.textSelected;
	}

	get coordinates(){
		return this.parent._coordinates;
	}

	get build(){
		return this.parent._build;
	}

	get clarify(){
		return this.parent._clarify;
	}

	get codonFetch(){
		return this.parent._codonFetch;
	}

	get selectionRange(){
		return this.parent.selectionRange;
	}

	get indexOf(){
		return this.parent._indexOf;
	}

	get ocr_correct(){
		return this.parent._ocr_correct;
	}

	get index(){
		return this.parent.index;
	}

	get undoes(){
		return this.parent.undoes;
	}

	set undoes(undoes){
		this.parent.undoes = undoes;
	}

	get adjust(){
		return this.parent._adjust;
	}

	get try_updating_codon(){
		return this.parent._try_updating_codon;
	}
}

console.log('import CounterPart.js');

export default CounterPart


