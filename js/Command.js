export class Command {

	constructor(func, ...args) {
		this.func = func;
		this.args = args;
	}

	run(){
		this.func(...this.args);
	}
}

export function modify_training(training, refresh_all){
	if (refresh_all) {
		if (training < 0) {
			training = ~training;
		}

		training |= 64;
	}
	else {
		if (training < 0)
			return training;
	}

	return ~training;
}

export function reset_training(training) {
	return training < 0? ~training & -65 : training;
}

export function set_training(self, refresh_all){
	var {index, $parent} = self;
	var {training} = $parent.data[index];
	$parent.data[index].training = modify_training(training, refresh_all);
}

export function command(self, refresh_all){
	var cmds = self.undoes;
	this.undoer.push(new Command(self=>{
		while (cmds.length)
			cmds.pop().run();

		if (self.async_render)
			self.async_render();

		self.$nextTick(()=>{
			self.focus();
		})
	}, self));

	self.undoes = [];

	set_training(self, refresh_all);
}

console.log('import Command.js');


