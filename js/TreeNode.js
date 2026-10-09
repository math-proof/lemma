class TreeNode {
    constructor(parent) {
		this.parent = parent;
    }

	Lexeme(){
		return new TreeNodeLexeme(...arguments);
	}

    static compile(infix) {
        var caret = new TreeNodeCaret();
        for (let i = 0; i < infix.length;) {
            switch (infix[i]) {
            case '{':
                caret = caret.append_left_brace();
                break;
            case '}':
                var old = caret;
                for (;;) {
                    if (caret == null) {
                        console.log(infix.substring(0, i));
                        console.log(infix.substring(i));
                        console.log("unnecessary right brace at position " + i);
                        caret = new TreeNodeBrace(old);
                        break;
                    }
                    old = caret;
                    caret = caret.parent;
                    if (caret instanceof TreeNodeBrace) {
                        break;
                    }
                }
                if (caret == null) {
                    caret = old;
                }

                break;
            default:
                var m = infix.slice(i).match(/[^{}]+/);
                if (!m)
                    throw "lexeme not found!";
                i += m[0].length + m.index;
                caret = caret.append_lexeme(m[0]);

                continue;
            }
            ++i;
        }

        for (;;) {
            if (caret.parent != null)
                caret = caret.parent;
            else
                break;
        }

        return caret;
    }

    replace(old, replacement) {
    }

    print() {
        var caret = this;
        while (caret != null) {
            console.log(caret);
            caret = caret.parent;
        }
        console.log();
    }

    toSyntacticTreeList(SyntacticTree, parent) {
        var arr = [];
        var node = this.toSyntacticTree(SyntacticTree, parent);
		if (node)
        	arr.push(node);
        return arr;
    }
}

class TreeNodeCaret extends TreeNode {
    get is_TreeNodeCaret(){
		return true;
	}

	constructor(parent){
		super(parent);
	}

    append_left_brace() {
		var parent = this.parent;
        var caret = new TreeNodeCaret();
        var parenthesis = new TreeNodeBrace(caret, parent);
        if (parent != null) {
            parent.replace(this, parenthesis);
        }
        return caret;
    }

    append_lexeme(lexeme) {
		var parent = this.parent;
        var caret = new TreeNodeLexeme(lexeme, parent);
        if (parent != null) {
            parent.replace(this, caret);
        }
        return caret;
    }

    toSyntacticTree() {
        console.log("TreeNodeCaret cannot be converted to SyntacticTree in toDependencyTreeList(SyntacticTree parent)");
        return null;
    }

    toString() {
        return "";
    }

    rawtext() {
        return "";
    }

    toSyntacticTreeList() {
        console.log("List<SyntacticTree> toSyntacticTreeList(SyntacticTree parent)");
        return [];
    }

}

class TreeNodeLexeme extends TreeNode {
    get is_TreeNodeLexeme(){
		return true;
	}

    constructor(lexeme, parent) {
		super(parent);
		this.lexeme = lexeme;
    }

    append_left_brace() {
		var parent = this.parent;
        var caret = new TreeNodeCaret();
        var replacement = new TreeNodePrefix(this.lexeme, new TreeNodeBrace(caret), parent);
        if (parent != null) {
            parent.replace(this, replacement);
        }
        return caret;
    }

    toSyntacticTree(SyntacticTree, parent) {
        var words = this.lexeme.trim().split(/ +/);
        var seg = null;
        var pos = null;
        var dep = null;
        var index = -1;
        switch (words.length) {
		case 1:
			[seg] = words;
			break;
		case 2:
			[seg, index] = words;
			index = parseInt(index);
			break;
		case 3:
			[seg, pos, dep] = words;
			break;
		case 4:
			[seg, pos, dep, index] = words;
			index = parseInt(index);
			break;
		}

        return new SyntacticTree(index, [seg, pos, dep], parent);
    }

    toString() {
        return this.lexeme;
    }

    rawtext() {
        return this.lexeme;
    }

    append_lexeme(lexeme) {
        return null;
    }
}

class TreeNodeBrace extends TreeNode {
    get is_TreeNodeBrace(){
		return true;
	}

	constructor(ptr, parent) {
		super(parent);
        this.ptr = ptr;
        this.ptr.parent = this;
    }

    append_lexeme(lexeme) {
		var parent = this.parent;
        if (parent instanceof TreeNodeArray) {
            return parent.append_lexeme(lexeme);
        }

        var suffix = new TreeNodeSuffix(lexeme, this, parent);
        if (parent != null) {
            parent.replace(this, suffix);
        }
        return suffix;
    }

    append_left_brace() {
		var parent = this.parent;

        if (parent != null && parent instanceof TreeNodeArray) {
            return parent.append_left_brace();
        }

        var caret = new TreeNodeCaret();
        var args = [];
        args.push(this);
        args.push(new TreeNodeBrace(caret));

        var mul = new TreeNodeArray(args, parent);
        if (parent != null) {
            parent.replace(this, mul);
        }
        return caret;
    }

    toSyntacticTree(SyntacticTree, parent) {
        return this.ptr.toSyntacticTree(SyntacticTree, parent);
    }

    toSyntacticTreeList(SyntacticTree, parent) {
        return this.ptr.toSyntacticTreeList(SyntacticTree, parent);
    }

    toString() {
        return '{' + this.ptr.toString() + '}';
    }

    rawtext() {
        return this.ptr.rawtext();
    }

    replace(old, replacement) {
        if (this.ptr != old)
            throw new "ptr != old";
        this.ptr = replacement;
    }
}

class TreeNodeArray extends TreeNode {
	get is_TreeNodeArray(){
		return true;
	}

    constructor(args, parent) {
		super(parent);
        this.args = args;
        for (let ptr of args) {
            ptr.parent = this;
        }
    }

    append_left_brace() {
        var caret = new TreeNodeCaret();
        this.args.push(new TreeNodeBrace(caret, this));
        return caret;
    }

    append_lexeme(lexeme) {
        var parent = this.parent;
        var suffix = new TreeNodeSuffix(lexeme, this, parent);
        if (parent != null) {
            parent.replace(this, suffix);
        }

        return suffix;
    }

    toSyntacticTree(SyntacticTree, parent) {
        console.log("TreeNodeMultiplication::toDependencyTree() is ambiguous.");
        var {args} = this;

        var tree = null;
        for (var index of range(args.length)) {
			if (tree = args[index].toSyntacticTree(SyntacticTree, parent)) {
		        var list = [];
		        for (let i of range(index + 1, args.length)) {
					var node = args[i].toSyntacticTree(SyntacticTree, tree);
					if (node)
		            	list.push(node);
		        }

				if (!tree.rhs)
					tree.rhs = [];

		        tree.rhs.push(...list);
		        return tree;
			}
		}
    }

    toSyntacticTreeList(SyntacticTree, parent) {
		var args = this.args;
        var list = [];
        for (let ptr of args) {
            if (ptr instanceof TreeNodeBrace) {
                var node = ptr.toSyntacticTree(SyntacticTree, parent);
                if (node)
                    list.push(node);
            } else
                throw new "SyntacticTree toDependencyTreeList()";
        }
        return list;
    }

    toString() {
        return this.args.map(el => el.toString()).join('');
    }

    rawtext() {
		return this.args.map(el => el.rawtext()).join('');
    }

    replace(old, replacement) {
        var i = this.args.indexOf(old);
        if (i < 0)
            throw new Error("replace(old, replacement)");
        this.args[i] = replacement;
    }
}

class TreeNodeBinary extends TreeNodeLexeme {
	get is_TreeNodeBinary(){
		return true;
	}

    constructor(lexeme, lhs, rhs, parent) {
        super(lexeme, parent);
        this.lhs = lhs;
        this.rhs = rhs;
        lhs.parent = rhs.parent = this;
    }

    append_left_brace() {
        throw new "TreeNode append_left_parenthesis()";
    }

    append_lexeme(lexeme) {
        return null;
    }

    toString() {
        return this.lhs.toString() + super.toString() + this.rhs.toString();
    }

    rawtext() {
        return this.lhs.rawtext() + super.rawtext() + this.rhs.rawtext();
    }

    replace(old, replacement) {
        if (this.lhs == old) {
            this.lhs = replacement;
        } else if (this.rhs == old) {
            this.rhs = replacement;
        } else
            throw new Error("replace(old, replacement)");
    }

    toSyntacticTree(SyntacticTree, parent) {
        var tree = super.toSyntacticTree(SyntacticTree, parent);
        tree.lhs = this.lhs.toSyntacticTreeList(SyntacticTree, tree);
        tree.rhs = this.rhs.toSyntacticTreeList(SyntacticTree, tree);
        return tree;
    }
}

class TreeNodePrefix extends TreeNodeLexeme {
	get is_TreeNodePrefix(){
		return true;
	}

    constructor(lexeme, caret, parent) {
        super(lexeme, parent);
        this.ptr = caret;
        this.ptr.parent = this;
    }

    append_left_brace() {
        throw new "TreeNode append_left_parenthesis()";
    }

    append_lexeme(lexeme) {
        return null;
    }

    toString() {
        return super.toString() + this.ptr.toString();
    }

    rawtext() {
        return super.rawtext() + this.ptr.rawtext();
    }

    replace(old, replacement) {
        if (this.ptr != old)
            throw new "ptr != old";
        this.ptr = replacement;
    }

    toSyntacticTree(SyntacticTree, parent) {
        var tree = super.toSyntacticTree(SyntacticTree, parent);
        tree.rhs = this.ptr.toSyntacticTreeList(SyntacticTree, tree);
        return tree;
    }
}

class TreeNodeSuffix extends TreeNodeLexeme {
	get is_TreeNodeSuffix(){
		return true;
	}

    constructor(lexeme, ptr, parent) {
        super(lexeme, parent);
        this.ptr = ptr;
        ptr.parent = this;
    }

    append_left_brace() {
        var caret = new TreeNodeCaret();
		var parent = this.parent;
        var replacement = new TreeNodeBinary(this.lexeme, this.ptr, new TreeNodeBrace(caret), parent);
        if (parent != null) {
            parent.replace(this, replacement);
        }
        return caret;
    }

    append_lexeme(lexeme) {
        return null;
    }

    toString() {
        return this.ptr.toString() + super.toString();
    }

    rawtext() {
        return this.ptr.rawtext() + super.rawtext();
    }

    replace(old, replacement) {
        if (this.ptr != old)
            throw new "ptr != old";
        this.ptr = replacement;
    }

    toSyntacticTree(SyntacticTree, parent) {
        var tree = super.toSyntacticTree(SyntacticTree, parent);
        tree.lhs = this.ptr.toSyntacticTreeList(SyntacticTree, tree);
        return tree;
    }
}

console.log('import TreeNode.js');

export default TreeNode
