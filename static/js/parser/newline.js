import {AbstractParser, IndentedNode, MatchTrait} from "./node.js"

class NewLine extends MatchTrait(IndentedNode) {
    case_newline(...kwargs) {
        this.indent = 0;
        ++this.newline_count
        return this;
    }

    case_space(...kwargs) {
        ++this.indent;
        return this;
    }

    case_tab(...kwargs) {
        this.indent += 4;
        return this;
    }
    
    case_default(key, ...kwargs) {
        var caret = this.parent;
        var self_kwargs = this.args;
        if (this.next)
            self_kwargs = [key, ...self_kwargs];
        return caret.parent.insert_newline(caret, this.newline_count, this.indent, ...self_kwargs).parse(key, ...kwargs);
    }
}

NewLine.case = {
    "\n": NewLine.prototype.case_newline,
    ' ': NewLine.prototype.case_space,
    "\t": NewLine.prototype.case_tab,
}

export default class NewLineParser extends AbstractParser {
    constructor(caret, next=null, ...args) {
        super(caret);
        this.caret = new NewLine(0, caret);
        this.caret.newline_count = 1;
        this.caret.next = next;
        this.caret.args = args;
    }
}

