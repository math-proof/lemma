export class Node {
    constructor(kwargs, parent = null) {
        this.kwargs = kwargs;
        this.parent = parent;
        this.args = [];
    }

    get indent() {
        return this.kwargs.indent;
    }

    set indent(indent) {
        this.kwargs.indent = indent;
    }

    get text() {
        return this.kwargs.text;
    }

    set text(text) {
        this.kwargs.text = text;
    }

    get start_idx() {
        return this.kwargs.start_idx;
    }

    set start_idx(start_idx) {
        this.kwargs.start_idx = start_idx;
    }

    get end_idx() {
        return this.kwargs.end_idx;
    }

    set end_idx(end_idx) {
        this.kwargs.end_idx = end_idx;
    }

    get kwargs_list() {
        return [];
    }

    static get base() {
        return this;
    }

    clone() {
        return new this.constructor(...this.kwargs_list, this.indent);
    }

    toString() {
        let str = this.strFormat();
        if (this.args.length > 0)
			return str.format(...this.args);
        return str;
    }

    get func() {
        return this.constructor.name;
    }

    append(newNode) {
        if (this.parent)
            return this.parent.append(newNode);
        throw new Error(`append is not defined for ${newNode} : ${this.constructor.name}`);
    }

    get root() {
        return this.parent ? this.parent.root : null;
    }

    toJSON() {
        return String(this);
    }

    get previousElementSibling() {
        if (!this.parent) return null;
        const index = this.parent.args.indexOf(this);
        return index > 0 ? this.parent.args[index - 1] : null;
    }

    remove() {
        if (this.parent)
            this.parent.removeChild(this);
    }

    replace(old, $new) {
        var i = this.args.indexOf(old);
        if (i < 0)
            throw new Error("replace is unexpected for " + get_class(this));

        if ($new.isArray) {
            this.args.splice(i, 1, ...$new);
            for (var el of $new)
                el.parent = this;
        } else {
            this.args[i] = $new;
            $new.parent = this;
        }
    }

    removeChild(node, deleteFlag = null) {
        const i = this.args.indexOf(node);
        if (i < 0) {
            console.log(`removeChild is unexpected for ${get_class(this)}`);
            return;
        }
        this.args.splice(i, 1);
        if (this.args.length === 1 && deleteFlag) {
            const [arg] = this.args;
            const parent = this.parent;
            if (parent) {
                parent.replace(this, arg);
                arg.parent = parent;
            }
        }
    }

    push(arg) {
        this.args.push(arg);
        arg.parent = this;
    }

    unshift(arg) {
        this.args.unshift(arg);
        arg.parent = this;
    }

    is_indented() {
        return false;
    }

    get bind() {
        return {
            args: this.args,
            kwargs : this.kwargs
        };
    }

    compareTo(index) {
        if (this.end_idx <= index.start_idx)
            return -1;
        if (this.start_idx >= index.end_idx)
            return 1;
        return 0;
    }

    parse(text, ...kwargs) {
        const fun = this.constructor.case[text];
        if (fun)
            return fun.call(this, ...kwargs);
        return this.case_default(text, ...kwargs);
    }

    *dfs_preorder() {
        yield this;
        for (const arg of this.args)
            yield* arg.dfs_preorder();
    }
    
    *dfs_preorder_reversed() {
        yield this;
        for (const arg of reversed(this.args))
            yield* arg.dfs_preorder_reversed();
    }
    
    *dfs_postorder() {
        for (const arg of this.args)
            yield* arg.dfs_postorder();
        yield this;
    }
    
    *dfs_postorder_reversed() {
        for (const arg of reversed(this.args))
            yield* arg.dfs_postorder_reversed();
        yield this;
    }
    
    *dfs(kwargs = {}) {
        let preorder;
        if (kwargs.preorder !== undefined)
            preorder = kwargs.preorder;
        else
            preorder = kwargs.postorder !== undefined? !kwargs.postorder: true;
        if (kwargs.reverse) {
            if (preorder)
                yield* this.dfs_preorder_reversed();
            else
                yield* this.dfs_postorder_reversed();
        } else {
            if (preorder)
                yield* this.dfs_preorder();
            else
                yield* this.dfs_postorder();
        }
    }
    *bfs(kwargs = {}) {
        let preorder;
        if (kwargs.preorder !== undefined)
            preorder = kwargs.preorder;
        else
            preorder = kwargs.postorder !== undefined? !kwargs.postorder: true;
    
        const {reverse} = kwargs;
        const queue = new Deque([this]);
        if (preorder) {
            while (queue.length > 0) {
                const node = queue.shift();
                yield node;
                queue.push(...(reverse? reversed(node.args): node.args));
            }
        } else {
            const levels = [];
            while (queue.length > 0) {
                const level_size = queue.length;
                const current_level = [];
                for (let _ of range(level_size)) {
                    const node = queue.shift();
                    current_level.push(node);
                    queue.push(...(reverse? reversed(node.args): node.args));
                }
                levels.push(current_level);
            }
            for (let level of reversed(levels))
                yield* level;
        }
    }
    *finditer(pred, kwargs = {}) {
        for (const node of this.dfs(kwargs)) {
            const val = pred(node);
            if (val != null) {
                if (val === true)
                    yield node;
                else if (val === false);
                else
                    yield val;
            }
        }
    }
    find_path(stop, pred, path) {
        if (stop) {
            var {args} = this;
            path.push('args');
            for (let i of range(stop - 1, -1, -1)) {
                path.push(i);
                var arg = args[i];
                if (pred(arg))
                    return true;
                if (arg instanceof Node && arg.args.length)
                    if (arg.find_path(arg.args.length, pred, path))
                        return true;
                path.pop();
            }
            path.pop();
        }
        if (this.parent) {
            if (path.length && Number.isInteger(path.back()))
                return;
            path.push('parent');
            if (this.parent.find_path(this.parent.args.indexOf(this), pred, path))
                return true;
            path.pop();
        }
    }
    static decompose_path(path) {
        var depth = 0;
        var i = 0;
        for (; i < path.length; ++i) {
            if (path[i] == 'parent')
                ++depth;
            else
                break;
        }

        var indices = [];
        for (; i < path.length; i += 2)
            indices.push(path[i + 1]);

        return {depth, indices};
    }
    search_tagBegin(pred, cls) {
        var {parent} = this;
        console.assert(parent.args.back() === this);
        var path = [];
        if (parent.find_path(parent.args.length - 1, pred, path)) {
//                                                 _____________________root________
//root.args[0]                    ____________root.args[1]  (....rest nodes)    root.args[-1]____
//             root.args[1][0] tagBegin                                                       tagEnd
            var tagBegin = getitem(parent, ...path);
            var {depth, indices} = cls.decompose_path(path);
//                                                 _____________________root_____________________
//root.args[0]                    ____________root.args[1]  (....rest nodes)    root.args[-1] tagEnd
//             root.args[1][0] tagBegin
            for (var _ of range(depth)) {
                this.parent.args.pop();
                this.parent.parent.args.push(this);
                this.parent = this.parent.parent;
            }
//                                                 ______________________root
//root.args[0]                    ____________root.args[1]_______________________________________
//             root.args[1][0] tagBegin                     (....rest nodes)    root.args[-1] tagEnd
            var start = indices.back();
            var {parent} = this;
            if (tagBegin.parent !== parent) {
                for (const node of this.parent.args.splice(indices[0] + 1))
                    tagBegin.parent.push(node);
                console.assert(tagBegin.parent === this.parent);
                parent.adjustment(this.parent, start);
            }
//                                                 _____________________root
//root.args[0]      __________________________root.args[1]__________________________
//             root.args[1][0]    _______________________________________________newTag__________
//                             tagBegin                     (....rest nodes)    root.args[-1] tagEnd
            var {args} = tagBegin.parent;
            console.assert(args[start] === tagBegin);
            start++;
            this.parent.replace(tagBegin, new cls([tagBegin, ...args.slice(start, -1), this]));
            // Remove elements from start to end of args
            args.splice(start);
            return tagBegin;
        }
    }
    setitem(i, val) {
        this.args[i] = val;
        val.parent = this;
    }
    adjustment(group, index) {
    }
}

export class AbstractParser {
    constructor(caret) {
        this.caret = caret;
    }

    parse(token, ...kwargs) {
        this.caret = this.caret.parse(token, ...kwargs);
        return this.caret;
    }

    static get instance() {
		if (!this._instance)
			this._instance = new this();
		return this._instance;
    }

    get func() {
        var {name} = this.constructor;
        if (name.endsWith("Parser"))
            // Remove 'Parser' suffix
            name = name.slice(0, -6).toLowerCase();
        return name;
    }

    get bind() {
        return {
            root: this.root
        };
    }

    *dfs() {
        yield this.root;
    }
}
AbstractParser.prototype.dfs_preorder = AbstractParser.prototype.dfs_preorder_reversed = AbstractParser.prototype.dfs_postorder = AbstractParser.prototype.dfs_postorder_reversed = AbstractParser.prototype.dfs;

export const Closable = (BaseClass) => class extends BaseClass {
    get is_closed() {
        return this.kwargs.is_closed;
    }

    set is_closed(is_closed) {
        this.kwargs.is_closed = is_closed;
    }
}

export class IndentedNode extends Node {
    constructor(indent = 0, parent = null) {
        super({indent}, parent);
    }    
}

export const MatchTrait = (BaseClass) => class extends BaseClass {
    static case = {};
}
