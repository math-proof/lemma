import {Command} from "./Command.js"

class Listener {

	constructor(context, obj) {
		this.obj = obj;
		this.context = context;
	}

	get listen(){
		return this.context.listen;
	}

	set(dict){
		for (let [prop, value] of Object.entries(dict)){
			this.command((obj, prop, value)=>{
				if (value == null)
					delete obj[prop];
				else
					obj[prop] = value;
			})(this.obj, prop, this.obj[prop])

			this.obj[prop] = value;
		}
	}

	get command(){
		if (!this._command) {
			var self = this.context;
			function _command(func){
				function push(){
					self.undoes.push(new Command(func, ...arguments));
				}
				return push;
			}
			this._command = _command;
		}

		return this._command;
	}

	set col(col){
		this.set({col});
	}

	set row(row){
		this.set({row});
	}

	set offsetStart(offsetStart){
		this.set({offsetStart});
	}

	set offsetStop(offsetStop){
		this.set({offsetStop});
	}

	set lineStart(lineStart){
		this.set({lineStart});
	}

	set lineStop(lineStop){
		this.set({lineStop});
	}

	set next(next){
		this.set({next});
	}

	set start(start){
		this.set({start});
	}

	set end(end){
		this.set({end});
	}

	set codon_id(id){
		var last = this.obj;
		do {
			var next = last.next;
			if (next == null){
				this.listen(last).id = id;
				break;
			}
			last = next;
		}
		while(last);
	}

	set codon_next(anotherCodon){
		var last = this.obj;
		do {
			var next = last.next;
			if (next == null){
				if (last.id){
					this.listen(anotherCodon).codon_id = last.id;
					this.listen(last).id.delete();
				}

				if (anotherCodon.type){
					this.listen(anotherCodon).type.delete();
				}

				this.listen(last).next = anotherCodon;
				break;
			}

			last = next;
		}
		while(last);
	}

	set src(src){
		this.set({src});
	}

	set seq(seq){
		this.set({seq});
	}

	set id(id){
		this.set({id});
	}

	set text(text){
		this.set({text});
	}

	set rowspan(rowspan){
		this.set({rowspan});
	}

	set colspan(colspan){
		this.set({colspan});
	}

	set align(align){
		this.set({align});
	}

	set valign(valign){
		this.set({valign});
	}

	set codon(codon){
		this.set({codon});
	}

	set sections(sections){
		this.set({sections});
	}

	set _codon(_codon){
		this.set({_codon});
	}

	set confidence(confidence){
		this.set({confidence});
	}

	set _confidence(_confidence){
		this.set({_confidence});
	}

	set training(training){
		this.set({training});
	}

	set is_predicted(is_predicted){
		this.set({is_predicted});
	}

	set type(type){
		this.set({type});
	}

	set head(head){
		this.set({head});
	}

	set entity(entity){
		this.set({entity});
	}

	getitem(attr){
		return new Property(this, attr);
	}

	get id(){
		return new Property(this, 'id');
	}

	get next(){
		return new Property(this, 'next');
	}

	get lineStart(){
		return new Property(this, 'lineStart');
	}
	get lineStop(){
		return new Property(this, 'lineStop');
	}

	get offsetStart(){
		return new Property(this, 'offsetStart');
	}
	get offsetStop(){
		return new Property(this, 'offsetStop');
	}

	get row(){
		return new Property(this, 'row');
	}

	get rowStart(){
		return new Property(this, 'rowStart');
	}
	get rowStop(){
		return new Property(this, 'rowStop');
	}

	get col(){
		return new Property(this, 'col');
	}

	get colStart(){
		return new Property(this, 'colStart');
	}
	get colStop(){
		return new Property(this, 'colStop');
	}

	get type(){
		return new Property(this, 'type');
	}

	get head(){
		return new Property(this, 'head');
	}

	insert(i, el){
		this.command((obj, i)=>{
			obj.delete(i);
		})(this.obj, i);

		return this.obj.insert(i, el);
	}

	push(){
		this.command((obj, size)=>{
			obj.splice(obj.length - size, size);
		})(this.obj, arguments.length);

		return this.obj.push(...arguments);
	}

	delete(i){
		this.command((obj, i, el)=>{
			if (Array.isArray(obj)){
				obj.insert(i, el);
			}
			else{
				obj[i] = el;
			}
		})(this.obj, i, this.obj[i]);

		if (Array.isArray(this.obj)){
			this.obj.delete(i);
		}
		else{
			delete this.obj[i];
		}
	}

	pop(){
		this.command((obj, el)=>{
			obj.push(el);
		})(this.obj, this.obj.back());

		return this.obj.pop();
	}

	setitem(i, value){
		this.command((obj, i, el, original_length)=>{
			if (original_length == null){
				if (el == null)
					delete obj[i];
				else
					obj[i] = el;
			}
			else{
				if (el == null && i >= original_length){
					obj.splice(original_length, obj.length - original_length);
				}
				else{
					obj[i] = el;
				}
			}
		})(this.obj, i, this.obj[i], this.obj.length);

		this.obj[i] = value;
	}

	back(value){
		this.command((obj, back)=>{
			obj.back(back);
		})(this.obj, this.obj.back());
		this.obj.back(value);
	}

	splice(){
		var [i, size, ...values] = arguments;
		this.command((obj, i, size, values)=>{
			obj.splice(i, size, ...values);
		})(this.obj, i, values.length, this.obj.slice(i, i + size));

		return this.obj.splice(i, size, ...values);
	}

	swap(i, j){
		this.command((obj, i, j)=>{
			obj.swap(i, j);
		})(this.obj, i, j);

		return this.obj.swap(i, j);
	}
}

class Property extends Listener {
	constructor(listener, prop) {
		super(listener.context, listener.obj);
		this.prop = prop;
	}

	delete(){
		this.command((obj, key, value)=>{
			obj[key] = value;
		})(this.obj, this.prop, this.obj[this.prop]);

		delete this.obj[this.prop];
	}

	increment(offset){
		if (offset == null){
			offset = 1;
		}

		this.command((obj, key, offset)=>{
			obj[key] -= offset;
		})(this.obj, this.prop, offset);

		this.obj[this.prop] += offset;
	}

	decrement(offset){
		if (offset == null){
			offset = 1;
		}

		this.command((obj, key, offset)=>{
			obj[key] += offset;
		})(this.obj, this.prop, offset);

		this.obj[this.prop] -= offset;
	}
}

console.log('import Listener.js');

export default Listener
