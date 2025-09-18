"use strict";

export function mounted(self) {
	document.addEventListener(
		'mousedown', 
		function(e) {
			if (e.button === 0) {
				console.log('Left mouse button clicked in document');
				self.click_left(e);
			}
		}
	);
}

export function click_left(event) {
	console.log("selectedIndex = ", this.selectedIndex);
	this.selectedIndex.clear();
}


export function has_typeclasses(lemma) {
	var {implicit, instImplicit} = lemma;
	if (instImplicit)
		return true;
	if (implicit) {
		for (var [, alpha] of implicit.matchAll(/\{\w+(?: \w+)* : ([\p{Script=Greek}a-zA-Z0-9_]+)\}/ug)) {
			if (alpha == 'Prop' || implicit.match(new RegExp(`\\{\\w+(?: \\w+)* : (Set|List) ${alpha}\\}`, 'u')))
				// alpha is Prop or a container of Set/List
				continue;
			return false;
		}
		return true;
	}
}

function latex_wrapper(list, hint, space) {
	hint = `-- ${hint}:`;
	if (list.length) {
		var latex = list.map(line => `\\[${line}\\]`);
		if (list.length > 1) {
			latex = latex.map(line => '-- ' + line);
			latex.unshift(hint);
			return latex.map(line => space + line).join("\n");
		}
		else
			return space + hint + ' ' + latex[0];
	}
}

function latex_annotation(latex, space) {
	if (!latex.isArray)
		latex = [latex];
	var Given = [];
	var Prove = [];
	for (var line of latex) {
		var [_, latex, color, tag] = line.match(/(.+)\\tag\*\{\$\\color\{(red|green)\}([^$]+)\$\}$/);
		(color == 'red'? Prove: Given).push(`${latex}\\tag*{$${tag}$}`);
	}
	latex = [];
	if (Given.length) {
		var hint = 'Premise';
		if (Given.length > 1)
			hint += 's';
		hint += " given";
		Given = latex_wrapper(Given, hint, space);
		latex.push(Given);
	}
	if (Prove.length) {
		var hint = 'Goal';
		if (Prove.length > 1)
			hint += 's';
		hint += " to prove";
		Prove = latex_wrapper(Prove, hint, space);
		latex.push(Prove);
	}
	return latex.join("\n");
}


export function fetch_lemma(lemma, lemmaType, using_latex=true, using_given=false, using_imply=false, using_proof=false) {
	lemmaType ||= 'lemma';
	var {comment, attribute, name, instImplicit, strictImplicit, implicit, given, explicit, imply, proof} = lemma;
	if (proof) {
		var by = proof.by ? 'by' : (proof.calc ? 'calc' : '');
		if (by)
			proof = proof[by];
		// proof = proof.map(line => line.lean);
	}
	if (comment) {
		var open_namespace = comment.match(/^open namespace in$/m);
		comment = `/--\n${comment}\n-/\n`;
		if (open_namespace)
			comment = `open ${name} in\n` + comment;
	}
	else
		comment = '';
	if (attribute && attribute.length) {
		attribute = attribute.join(", ")
		attribute = `@[${attribute}]\n`;
	}
	else
		attribute = '';
	var declspec = [];
	if (instImplicit) {
		if (!proof) {
			var alphaSet = {};
			for (var [, typeclass, alpha] of instImplicit.matchAll(/\[(\w+) ([\p{Script=Greek}a-zA-Z0-9_]+)\]/ug)) {
				if (typeclass == 'Decidable');
				else
					alphaSet[alpha] = true;
			}
			var alphaSet = Object.keys(alphaSet);
			if (alphaSet.length)
				declspec.push(`  {${alphaSet.join(' ')} : Type _}`);
		}
		declspec.push(instImplicit.replace(/^/mg, '  '));
	}
	if (implicit)
		declspec.push(implicit.replace(/^/mg, '  '));

	if (given) {
		if (using_given)
			declspec.push("-- given");
		given = given.map(line => line.lean.replace(/^/mg, '  '));
		declspec.push(...given);
	}

	if (explicit)
		declspec.push(explicit.replace(/^/mg, '  '));

	declspec = declspec.join("\n");
	imply = imply.lean.replace(/^/mg, '  ');

	if (declspec) {
		declspec = `\n${declspec}`;
		if (!given && !explicit)
			declspec += ' :';
	}
	else 
		declspec = ' :';
	var using_imply = using_imply? "-- imply\n": "";
	var code = `${comment}${attribute}${lemmaType} ${name}${declspec}
${using_imply}${imply}`;
	if (proof) {
		proof = proof.map(code => {
			var {lean, latex} = code;
			code = lean.replace(/^/mg, '  ');
			if (latex && using_latex) {
				var space = '';
				for (var line of code.split("\n")) {
					if (line.match(/ *-- */))
						continue;
					space = line.match(/^ +/)[0];
				}
				if (code.endsWith('·'))
					space += '  ';
				code += "\n" + latex_annotation(latex, space);
			}

			return code;
		});
		proof = proof.join("\n").ltrim("\n");
		proof = proof.rtrim();
		using_proof = using_proof? "-- proof\n": "";
		code += `\n${using_proof}${proof}`;
	}
	return code;
}


console.log("import lemma.js");