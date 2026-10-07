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
    /**
     * `ℙ[…](…)` / `𝔼[…](…)` (mirrors JS `isProbExpectEventParen`): also `ℙ[π](…).toReal`
     * and mid-juxtaposition `∇[θ] ℙ[π](…).toReal`.
     */
    public function isProbExpectParen()
    {
        $isHead = function ($n) {
            return $n instanceof LeanGetElem && $n->args[0] instanceof LeanToken && in_array($n->args[0]->text, ['ℙ', '𝔼'], true);
        };
        $self = $this;
        $p = $this->parent;
        if ($p instanceof LeanProperty && $p->args[0] === $this) {
            $self = $p; // `….toReal`
            $p = $p->parent;
        }
        if (!($p instanceof LeanArgsSpaceSeparated))
            return false;
        $i = array_search($self, $p->args, true);
        if ($i === false || $i < 1)
            return false;
        return $isHead($p->args[$i - 1]);
    }

    /** Rendered as `\left(…\right)` (not elided / not a multi-row block), so a `\middle` may sit inside. */
    public function isLatexStretchy()
    {
        return $this->latexFormat() === $this->toColor();
    }

    /**
     * The conditioning `|` directly inside these parentheses: `𝔼[…](body | cond)`, `𝔼[…](body | y, z)`,
     * `ℙ[…](x = a | y = b)` or `(X ⟂ᵢ Y | Z)`; null when the parentheses do not stretch.
     */
    public function conditioningBar()
    {
        $arg = $this->arg;
        $probExpect = $this->isProbExpectParen();
        if ($arg instanceof LeanBitOr)
            $bar = $arg;
        elseif ($probExpect && $arg instanceof LeanArgsCommaSeparated && $arg->args[0] instanceof LeanBitOr)
            $bar = $arg->args[0];
        else
            return null;
        if (!$probExpect && !LeanIndep::independenceOf($bar->args[0]))
            return null;
        return $this->isLatexStretchy() ? $bar : null;
    }

    /**
     * `\middle|` must be at the same group level as its `\left(` / `\right)`, so the bar goes directly into the
     * paren body, not inside the `{…}` group of LeanBitOr / LeanArgsCommaSeparated (mirrors JS `conditioningLatex`).
     */
    public function conditioningLatex(&$syntax = null)
    {
        $bar = $this->conditioningBar();
        if (!$bar)
            return null;
        [$lhs, $rhs] = $bar->latexArgs($syntax);
        $parts = ["{{$lhs}} \\,\\middle|\\, {{$rhs}}"];
        if ($bar !== $this->arg)
            foreach (array_slice($this->arg->args, 1) as $a)
                $parts[] = '{' . $a->toLatex($syntax) . '}';
        return [implode(', ', $parts)];
    }

    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        $conditioning = $this->conditioningLatex($syntax);
        if ($conditioning)
            return $conditioning;
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
     * Parentheses only needed for Lean parsing (e.g. `(γ ^ id) @ r[t:]`): the inner operator
     * binds tighter than the surrounding one, so LaTeX can drop the parens (`γ^{id} × r_{t:}`).
     */
    public function isLatexRedundantPrecedence()
    {
        $p = $this->parent;
        if (!($p instanceof LeanArithmetic))
            return false;
        $arg = $this->arg;
        if (!($arg instanceof LeanArithmetic))
            return false;
        $childPri = get_class($arg)::$input_priority ?? 0;
        $parentPri = get_class($p)::$input_priority ?? 0;
        return $childPri > $parentPri;
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
        if ($p instanceof LeanArgsSpaceSeparated ||
            $p instanceof LeanArgsCommaSeparated ||
            $p instanceof LeanGetElem ||
            $p instanceof LeanGetElemQue ||
            $p instanceof LeanGetElemQuote ||
            $p instanceof LeanRelational)
            return true;
        // ENNReal→ℝ (`open scoped ENNReal.ToRealCoe`): `(ℙ[…](…) : ℝ)` under `•` / `+` / …
        if ($arg->rhs instanceof LeanToken && $arg->rhs->text === 'ℝ' && $p instanceof LeanArithmetic)
            return true;
        return false;
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
    /**
     * Structure-instance literal with its first field on the `{` line (mirrors paired.js LeanBrace.inline):
     *     { toFun := f
     *       invFun := g }
     * Set once the body became a `structInst` LeanStatements; printed `{ … }` so the continuation lines keep
     * the first field's column (Lean `sepByIndent`).
     */
    public $inline = null;

    /** Column of a `}` written on its own line after an `inline` body. */
    public $closeIndent = null;

    /** A field (`x := v`), or a comma list of fields ending in a comma (`a := 1, b := 2,`). */
    public static function isStructInstField($node)
    {
        if ($node instanceof LeanAssign)
            return true;
        if (!($node instanceof LeanArgsCommaSeparated))
            return false;
        $any = false;
        foreach ($node->args as $a) {
            if ($a instanceof LeanAssign)
                $any = true;
            elseif (!($a instanceof LeanCaret))
                return false;
        }
        return $any;
    }

    /** Parent that holds structure-instance fields: a brace, a `{ s with … }` update, or a `structInst` body. */
    public static function isStructInstOwner($node)
    {
        return $node instanceof LeanBrace ||
            ($node instanceof LeanWith && $node->isStructUpdate()) ||
            ($node instanceof LeanStatements && $node->structInst === true);
    }

    /** Turn the single field `$current` of `$owner` into a `structInst` body at column `$indent`; returns [body, caret]. */
    public static function openStructInstBody($owner, $current, $newline_count, $indent)
    {
        $current->indent = $indent;
        $stmts = new LeanStatements([$current], $indent, $current->level);
        $stmts->structInst = true;
        $out = null;
        for ($i = 0; $i < max($newline_count, 1); ++$i) {
            $out = new LeanCaret($indent, $stmts->level);
            $stmts->push($out);
        }
        return [$stmts, $out];
    }

    /** `{ s with⏎ … }` / `{ s with a := 1⏎ … }` whose `with` got a multi-line body. */
    public function structUpdateWith()
    {
        $a = $this->arg;
        $w = $a instanceof LeanArgsSpaceSeparated ? end($a->args) : null;
        return $w instanceof LeanWith && $w->args[0] instanceof LeanStatements && $w->args[0]->structInst === true ? $w : null;
    }

    /** Multi-line structure literal: printed with Lean's `{ … }` spacing. */
    public function isSpacedStructInst()
    {
        return $this->inline === true || $this->structUpdateWith() !== null;
    }

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
        if ($indent > $this->indent && $caret === $this->arg && !($caret instanceof LeanCaret) &&
            !($caret instanceof LeanStatements) && self::isStructInstField($caret)) {
            // first field on the `{` line, next field on the next line: keep its column (`$indent`), not `indent + 2`
            [$stmts, $out] = self::openStructInstBody($this, $caret, $newline_count, $indent);
            $this->arg = $stmts;
            $this->inline = true;
            return $out;
        }
        if ($this->inline && $indent == $this->indent && $next == '}' && $this->closeIndent === null) {
            // `{ a := 1⏎ … b := 2⏎ }`: the closing brace on a line of its own
            $this->closeIndent = $indent;
            return $caret;
        }
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
        return !($parent instanceof LeanQuantifier || $parent instanceof LeanBinaryBoolean || $parent instanceof LeanColon || $parent instanceof LeanSetOperator || $parent instanceof LeanTactic || $parent instanceof LeanAssign ||
            // `⟨{ toFun := … }, e⟩` / `({ … }, n)`: an inline brace, not a line of its own (was `⟨    {`)
            $parent instanceof LeanArgsCommaSeparated || $parent instanceof LeanPairedGroup);
    }

    public function set_line($line)
    {
        if (!$this->inline)
            return parent::set_line($line);
        // `{ first⏎ … }`: the body starts on the `{` line and the `}` closes the last field's line
        $this->line = $line;
        $line = $this->arg->set_line($line);
        return $this->closeIndent !== null && $this->is_closed ? $line + 1 : $line;
    }

    public function strFormat()
    {
        if (!$this->isSpacedStructInst())
            return parent::strFormat();
        $format = $this->argFormat();
        $close = $this->closeIndent !== null ? "\n" . str_repeat(' ', $this->closeIndent) . '}' : ' }';
        if ($this->is_closed)
            return '{ ' . $format . $close;
        if ($this->is_closed === null)
            return '{ ' . $format;
        return $format . $close;
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

// END OF paired family (LeanParser stays in lean.php)
