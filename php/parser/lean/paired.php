<?php
/**
 * Paired delimiters (`LeanPairedGroup` and parenthesis, bracket, brace, abs,
 * norm, ceil, floor, and angle quotations).
 *
 * Loaded by lean.php after LeanUnary and the Closable trait exist.
 * Mirrors static/js/parser/lean/paired.js. Not a standalone entry point.
 */

abstract class LeanPairedGroup extends LeanUnary
{
    use Closable;
    public static $input_priority = 60;
    public function argFormat() {
        return '%s';
    }
    public function insert($caret, $func, $type)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->arg = new $func($caret, $this->indent, $caret->level);
                return $caret;
            }
            if ($caret instanceof LeanToken) {
                $caret = new LeanCaret($this->indent, $caret->level);
                $this->arg = new LeanArgsSpaceSeparated([$this->arg, new $func($caret, $this->indent, $caret->level)], $this->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function insert_comma($caret)
    {
        $caret = new LeanCaret($this->indent, $caret->level);
        if ($caret instanceof LeanArgsCommaSeparated)
            $this->arg->push($caret);
        else
            $this->arg = new LeanArgsCommaSeparated([$this->arg, $caret], $this->indent, $caret->level);
        return $caret;
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanArgsCommaNewLineSeparated(
                    [new LeanArgsCommaSeparated([$caret], $indent, $caret->level)],
                    $indent,
                    $caret->level
                );
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_Expr() {
        return true;
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return !($parent instanceof LeanTactic || 
            $parent instanceof LeanArgsCommaSeparated || 
            $parent instanceof LeanAssign || 
            $parent instanceof LeanArgsSpaceSeparated || 
            $parent instanceof LeanRelational || 
            $parent instanceof LeanRightarrow || 
            $parent instanceof LeanUnaryArithmeticPre || 
            $parent instanceof LeanArithmetic || 
            $parent instanceof LeanProperty || 
            $parent instanceof LeanColon || 
            $parent instanceof LeanUnaryArithmeticPost || 
            $parent instanceof LeanPairedGroup ||
            $parent instanceof LeanGetElem ||
            $parent instanceof LeanGetElemQue ||
            $parent instanceof LeanGetElemQuote
        );
    }

    public function push_right($func)
    {
        if (get_class($this) == $func) {
            $this->is_closed = true;
            return $this;
        }
        return $this->parent->push_right($func);
    }

    public function set_line($line)
    {
        $this->line = $line;
        $arg = $this->arg;
        if ($has_newline = ($arg instanceof LeanArgsCommaNewLineSeparated || $arg instanceof LeanStatements))
            ++$line;
        $line = $arg->set_line($line);
        if ($has_newline)
            ++$line;
        return $line;
    }

    public function strFormat()
    {
        $format = $this->argFormat();
        $operator = $this->operator;
        if ($this->is_closed)
            $format = $operator[0] . $format . $operator[1];
        else if ($this->is_closed === null)
            $format = $operator[0] . $format;
        else 
            $format .= $operator[1];
        return $format;
    }

}

class LeanParenthesis extends LeanPairedGroup
{
    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct($arg, $indent, $level, $parent);
        ++$this->arg->level;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            case 'operator':
                return '()';
            default:
                return parent::__get($vname);
        }
    }

    public function append($new, $func)
    {
        $indent = $this->indent;
        $level = $this->level;
        $caret = new LeanCaret($indent, $level);
        if (is_string($new)) {
            $new = new $new($caret, $indent, $level);
            if ($this->parent instanceof LeanArgsSpaceSeparated)
                $this->parent->push($new);
            else
                $this->arg = new LeanArgsSpaceSeparated([$this->arg, $new], $indent, $level);
            return $caret;
        } else {
            $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent, $level));
            return $new;
        }
    }

    public function argFormat() {
        $arg = $this->arg;
        if ($arg instanceof LeanBy && ($stmt = $arg->arg) instanceof LeanStatements && end($stmt->args) instanceof LeanCaret) {
            $indent = str_repeat(' ', $this->indent);
            return "%s$indent";
        } else
            return '%s';
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret === $this->arg) {
                if ($caret instanceof LeanBy && $this->indent == $indent) {
                    $caret = new LeanCaret($indent, $caret->level);
                    $new = new LeanArgsNewLineSeparated([$this->arg, $caret], $indent, $caret->level);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->arg = $new;
                } else {
                    if ($this->indent == $indent)
                        $indent = $this->indent + 2;
                    $caret = $this->push_args_indented($indent, $newline_count, false);
                }
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_unary($caret, $func)
    {
        if ($caret === $this->arg) {
            $indent = $this->indent;
            if ($caret instanceof LeanCaret)
                $new = new $func($caret, $indent, $caret->level);
            else {
                $level = $caret->level;
                $caret = new LeanCaret($indent, $level);
                $new = new LeanArgsSpaceSeparated([$this->arg, new $func($caret, $indent, $level)], $indent, $level);
            }
            $this->arg = $new;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        $parent = $this->parent;
        if ($parent instanceof LeanColon && ($gr = $parent->parent) instanceof LeanModule) {
            $rhs = $parent->rhs;
            if ($rhs instanceof LeanStatements
                && count($rhs->args) === 1
                && ($c = $rhs->args[0]) instanceof LeanLineComment
                && $c->text === 'imply'
            ) {
                $ix = array_search($parent, $gr->args, true);
                if ($ix !== false && $ix + 1 < count($gr->args) && $gr->args[$ix + 1] instanceof Lean_let) {
                    return true;
                }
            }
        }
        return $parent instanceof LeanArgsNewLineSeparated || $parent instanceof LeanArgsCommaNewLineSeparated || ($parent instanceof LeanIte && $this !== $parent->if);
    }

    public function isMatMulContext()
    {
        return $this->parent && $this->parent->isMatMulContext();
    }

    public function isProp($vars)
    {
        return $this->arg->isProp($vars);
    }
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg->matrixLatexSpec())
            return [$arg->toLatex($syntax)];
        if ($arg instanceof LeanColon) {
            if ($arg->lhs instanceof LeanBrace)
                return $arg->lhs->latexArgs($syntax);
            if ($arg->rhs instanceof LeanToken && $arg->rhs->text == 'Bool')
                return [$arg->lhs->toLatex($syntax)];
            if ($arg->isZeroOneTensor())
                return [$arg->toLatex($syntax)];
            if ($this->isLatexArgAscription())
                return [$arg->lhs->toLatex($syntax)];
        }
        if ($this->isLatexGetElemOperand())
            return [$arg->toLatex($syntax)];
        if ($this->isLatexRedundantPrecedence())
            return [$arg->toLatex($syntax)];
        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        $arg = $this->arg;
        if ($arg->matrixLatexSpec())
            return '%s';
        if ($arg instanceof LeanColon) {
            if ($arg->lhs instanceof LeanBrace)
                return $arg->lhs->latexFormat(); # special case for ({ ... } : ...)
            if ($arg->rhs instanceof LeanToken && $arg->rhs->text == 'Bool')
                return '\left|{%s}\right|';
            if ($arg->isZeroOneTensor())
                return '%s';
            if ($this->isLatexArgAscription())
                return '%s';
        }
        if ($this->isLatexGetElemOperand())
            return '%s';
        if ($this->isLatexRedundantPrecedence())
            return '%s';
        return $this->toColor();
    }

    /**
     * `(γ ^ id) * r` — the inner op binds tighter than the parent, so the
     * parens are only a parse grouping. Drop the colorbox / `\left(\right)`.
     * `(a + b) * c` keeps them: `+` binds looser than `*`.
     */
    public function isLatexRedundantPrecedence()
    {
        $parent = $this->parent;
        $child = $this->arg;
        if (!($parent instanceof LeanArithmetic && $child instanceof LeanArithmetic))
            return false;
        return get_class($child)::$input_priority > get_class($parent)::$input_priority;
    }

    public function isLatexGetElemOperand()
    {
        $p = $this->parent;
        return $p instanceof LeanGetElem ||
            $p instanceof LeanGetElemQue ||
            $p instanceof LeanGetElemQuote;
    }

    public function isLatexArgAscription()
    {
        $arg = $this->arg;
        if (!($arg instanceof LeanColon))
            return false;
        if ($arg->isZeroOneTensor())
            return false;
        if ($arg->lhs instanceof LeanBrace)
            return false;
        if ($arg->rhs instanceof LeanToken && $arg->rhs->text == 'Bool')
            return false;
        $p = $this->parent;
        return $p instanceof LeanArgsSpaceSeparated ||
            $p instanceof LeanArgsCommaSeparated ||
            $p instanceof LeanGetElem ||
            $p instanceof LeanGetElemQue ||
            $p instanceof LeanGetElemQuote ||
            $p instanceof LeanRelational;
    }

    public function peelLatexCoe()
    {
        $inner = $this->arg->peelLatexCoe();
        if ($inner !== $this->arg)
            return $inner;
        return $this;
    }

    public function peelParen()
    {
        if ($this->arg instanceof LeanColon)
            return $this;
        return $this->arg->peelParen();
    }

    public function peelGroup()
    {
        return $this->arg->peelGroup();
    }

    public function regexp()
    {
        return $this->arg->regexp();
    }

    public function toColor(): string
    {
        $n = $this->arg->level & 7;
        $b = "9f"[$n & 1];
        $n >>= 1;
        $g = "9f"[$n & 1];
        $n >>= 1;
        $r = "9f"[$n & 1];
        // for katex:
        return "\\colorbox{#{$r}{$g}{$b}}{\$\\mathord{\\left(%s\\right)}\$}";
        // for mathjax:
        // return "\\bbox[#{$r}{$g}{$b}]{\\left(%s\\right)}";
    }

}

class LeanAngleBracket extends LeanPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            case 'operator':
                return ['⟨', '⟩'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\langle {%s} \rangle';
    }

    public function push_token($word)
    {
        $level = $this->level;
        $new = new LeanToken($word, $this->indent, $level);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent, $level));
        return $new;
    }
    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LeanArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
    }

    public function tokens_comma_separated()
    {
        $tokens = [];
        $arg  = $this->arg;
        if ($arg instanceof LeanArgsCommaSeparated)
            $tokens = $arg->tokens_comma_separated();
        else
            $tokens = [$arg];
        return $tokens;
    }

}

class LeanBracket extends LeanPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '[]';
            default:
                return parent::__get($vname);
        }
    }
    public function is_Expr() {
        return false;
    }

    public function latexFormat()
    {
        return '\left[ {%s} \right]';
    }

    public function push_right($func)
    {
        if (get_class($this) == $func && ($lt = $this->arg) instanceof Lean_lt && $lt->lhs instanceof LeanToken) {
            $level = $this->level;
            $new = new LeanStack($lt, $this->indent, $level);
            $caret = new LeanCaret($this->indent, $level);
            $new->scope = $caret;
            $this->parent->replace($this, $new);
            return $caret;
        }
        if (get_class($this) == $func && ($lim = $this->parent) instanceof Lean_lim && $lim->bound === $this && !$lim->scope) {
            $lim->bound = $this->arg;
            $caret = new LeanCaret($this->indent, $this->level);
            $lim->scope = $caret;
            return $caret;
        }
        return parent::push_right($func);
    }
    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LeanArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
    }

}

class LeanBrace extends LeanPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '{}';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanStatements([$caret], $indent, $caret->level);
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
    public function is_Expr() {
        return false;
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return !($parent instanceof LeanQuantifier || $parent instanceof LeanBinaryBoolean || $parent instanceof LeanColon || $parent instanceof LeanSetOperator || $parent instanceof LeanTactic || $parent instanceof LeanAssign);
    }

    public function latexFormat()
    {
        return '\left\{ {%s} \right\}';
    }

}

class LeanAbs extends LeanPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '||';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_bar($caret, $prev_token, $next)
    {
        return $this->push_right('LeanAbs');
    }
    public function latexFormat()
    {
        return '\left| {%s} \right|';
    }

}

class LeanNorm extends LeanPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return ['‖', '‖'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lVert {%s} \right\rVert';
    }
}

class LeanCeil extends LeanPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['⌈', '⌉'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lceil {%s} \right\rceil';
    }
}

class LeanFloor extends LeanPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['⌊', '⌋'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lfloor {%s} \right\rfloor';
    }
}

class LeanSingleAngleQuotation extends LeanPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            case 'operator':
                return ['‹', '›'];
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        return '\text{‹}{%s}\text{›}';
    }
}

class LeanDoubleAngleQuotation extends LeanPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['«', '»'];
            default:
                return parent::__get($vname);
        }
    }

    public function is_Expr() {
        return false;
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        return '{\\color{red}%s}';
    }
}

// END OF paired family (LeanBinaryBoolean stays in lean.php)
