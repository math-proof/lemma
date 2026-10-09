class Undoer {

	constructor() {
		this.stack = [];
	}

	push(cmd){
		this.stack.push(cmd);
	}

	get length(){
		return this.stack.length;
	}

	peek(){
		return this.stack.back();
	}

	pop(){
		return this.stack.pop();
	}

	undo() {
		if (this.length) {
			var peek = this.pop();
			if (typeof peek == 'function')
				return peek();

			return peek.run();
		}

		return false;
	}

	redo() {
		// TODO
	}
}

console.log('import Undoer.js');

export default Undoer
