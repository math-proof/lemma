<?php
/**
 * Big operators (`LeanBigOperator`, `∑`, `lim`, `∏`, `∫`, `∂`, `∇`, `𝔼`, `ℙ`, `𝕍𝕒𝕣`, `⋂`, `⋃`, `Stack`).
 *
 * Loaded by lean.php after `fun.php` and before `quantifier.php`, because
 * `LeanQuantifier` extends `LeanBigOperator`.
 * JS also has `LeanInf` / `LeanSup` (`⨅` / `⨆`); this file does not.
 * Mirrors js/parser/lean/bigops.js. Not a standalone entry point.
 */

class LeanBigOperator extends LeanArgs
{
    public function __construct($bound, $indent, $level, $parent = null)
    {
        parent::__construct([$bound], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'bound':
                // bound variable or quantified variable.
                return $this->args[0];
            case 'scope':
                // body or scope of the quantifier.
                return $this->args[1] ?? null;
            case 'stack_priority':
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'bound':
                $this->args[0] = $val;
                break;
            case 'scope':
                $this->args[1] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    /**
     * `∫ x : ℝ in a..b, f x` — the `in` domain modifier attaches to the bound as a sibling:
     * bound becomes `LeanArgsSpaceSeparated [oldBound, LeanIn domain]`.
     */
    public function insert($caret, $func, $type)
    {
        if ($func === 'LeanIn' && $type === 'modifier' && $caret === $this->bound && $this->scope === null) {
            $c = new LeanCaret($this->indent, $caret->level);
            $domain = new LeanIn($c, $this->indent, $caret->level);
            $this->bound = new LeanArgsSpaceSeparated([$caret, $domain], $this->indent, $caret->level);
            return $c;
        }
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->bound) {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->scope = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_if($caret)
    {
        if ($this->scope === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->scope = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->scope) {
            // Continue trailing app in scope across newline under forall/exists.
            if ($caret instanceof LeanArgsSpaceSeparated) {
                if ($cont = $caret->push_args_indented($indent, $newline_count))
                    return $cont;
            }
            if ($new = $this->push_args_indented($this->indent + 2, $newline_count))
                return $new;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
    public function is_indented()
    {
        return ($parent = $this->parent) instanceof LeanStatements || $parent instanceof LeanIte;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => parent::jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        return "$this->command\\limits_{\\substack{%s}} {%s}";
    }

    public function strFormat()
    {
        if (count($this->args) == 1)
            return "$this->operator %s,";
        return "$this->operator %s, %s";
    }

}

class Lean_sum extends LeanBigOperator
{
    public static $input_priority = 67;
    /** `∑'` (`tsum` over a possibly infinite type) versus plain `∑` (`Finset.sum`). */
    public $prime = false;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return $this->prime ? "∑'" : '∑';
            default:
                return parent::__get($vname);
        }
    }

    /** Display-only: nested `∑ i, ∑ j, body` → one ∑ with stacked limits. */
    public function nestedSumChain()
    {
        if ($this->prime)
            return null;
        $chain = [$this];
        $cur = $this;
        while (true) {
            $next = $cur->scope;
            while ($next instanceof LeanParenthesis)
                $next = $next->arg;
            if (!($next instanceof Lean_sum) || $next->prime)
                break;
            $chain[] = $next;
            $cur = $next;
        }
        if (count($chain) < 2)
            return null;
        return ['chain' => $chain, 'body' => $cur->scope];
    }

    public function latexArgs(&$syntax = null)
    {
        $nested = $this->nestedSumChain();
        if ($nested) {
            $limits = [];
            // Inner binder first (evaluation / sympy substack order), then outer.
            foreach (array_reverse($nested['chain']) as $s)
                $limits[] = $s->bound->toLatex($syntax);
            return [implode(' \\\\ ', $limits), $nested['body']->toLatex($syntax)];
        }
        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        if ($this->nestedSumChain())
            return "\\sum\\limits_{\\substack{%s}} {%s}";
        if (!$this->prime)
            return parent::latexFormat();
        // `\sum'` carries the prime as a superscript; wrap in `\mathop` to keep
        // the bound below (`\limits`) like the plain `\sum` case.
        return "\\mathop{\\sum'}\\limits_{\\substack{%s}} {%s}";
    }
}

class Lean_lim extends LeanBigOperator
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'lim';
            case 'command':
                return '\\lim';
            case 'stack_priority':
                if ($this->scope)
                    return 67;
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }
    /** `lim [N → ∞] ∑ n ∈ range N, e` → infinite sum from `n = 0`. */
    public function asInfiniteRangeSum()
    {
        $unwrap = function ($n) {
            while ($n instanceof LeanParenthesis)
                $n = $n->arg;
            return $n;
        };
        $isInf = function ($n) use ($unwrap) {
            $n = $unwrap($n);
            if ($n instanceof LeanToken)
                return $n->text === '∞';
            if ($n instanceof LeanPlus) {
                $arg = $unwrap($n->arg);
                return $arg instanceof LeanToken && $arg->text === '∞';
            }
            return false;
        };
        $isRangeFn = function ($fn) use ($unwrap) {
            $fn = $unwrap($fn);
            if ($fn instanceof LeanToken)
                return $fn->text === 'range';
            return $fn instanceof LeanProperty && $fn->rhs instanceof LeanToken && $fn->rhs->text === 'range';
        };
        $isRangeOf = function ($node, $n) use ($unwrap, $isRangeFn) {
            $node = $unwrap($node);
            if (!($node instanceof LeanArgsSpaceSeparated) || count($node->args) !== 2)
                return false;
            $arg = $unwrap($node->args[1]);
            return $isRangeFn($node->args[0]) && $arg instanceof LeanToken && $n instanceof LeanToken && $arg->text === $n->text;
        };
        $bound = $unwrap($this->bound);
        if (!($bound instanceof Lean_rightarrow) || !$isInf($bound->rhs))
            return null;
        $nLim = $unwrap($bound->lhs);
        if (!($nLim instanceof LeanToken))
            return null;
        $sum = $unwrap($this->scope);
        if (!($sum instanceof Lean_sum))
            return null;
        $mem = $unwrap($sum->bound);
        if (!($mem instanceof Lean_in) || !$isRangeOf($mem->rhs, $nLim))
            return null;
        return ['index' => $mem->lhs, 'body' => $sum->scope];
    }
    public function latexFormat()
    {
        if ($this->asInfiniteRangeSum())
            return '\\sum\\limits_{%s=0}^{\\infty} {%s}';
        return "$this->command\\limits_{%s} {%s}";
    }
    public function latexArgs(&$syntax = null)
    {
        if ($inf = $this->asInfiniteRangeSum())
            return [$inf['index']->toLatex($syntax), $inf['body']->toLatex($syntax)];
        return parent::latexArgs($syntax);
    }
    public function strFormat()
    {
        if (count($this->args) == 1)
            return "$this->operator [%s]";
        return "$this->operator [%s] %s";
    }
}

class Lean_prod extends LeanBigOperator
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∏';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_int extends LeanBigOperator
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∫';
            default:
                return parent::__get($vname);
        }
    }

    /** The `x : ℝ` binder, peeling the space-separated domain wrapper and parentheses. */
    private function binderColon()
    {
        $b = $this->bound;
        if ($b instanceof LeanArgsSpaceSeparated)
            $b = $b->args[0];
        if ($b instanceof LeanParenthesis)
            $b = $b->arg;
        return $b instanceof LeanColon ? $b : null;
    }

    /** Domain after `in`, if any (e.g. `a..b` or `Ioc a b`). */
    private function intDomain()
    {
        $b = $this->bound;
        if ($b instanceof LeanArgsSpaceSeparated) {
            foreach ($b->args as $a) {
                if ($a instanceof LeanIn)
                    return $a->arg;
            }
        }
        return null;
    }

    /** Find the trailing `∂μ` measure node in the scope, if any. */
    private function measurePartial()
    {
        $s = $this->scope;
        if ($s instanceof LeanArgsSpaceSeparated) {
            for ($i = count($s->args) - 1; $i >= 0; $i--) {
                if ($s->args[$i] instanceof LeanCaret) continue;
                return $s->args[$i] instanceof Lean_partial ? $s->args[$i] : null;
            }
            return null;
        }
        // Binary operator scope (e.g. `c • f x ∂μ` → Lean_bullet(c, LeanArgsSpaceSeparated[f, x, ∂μ]))
        if ($s !== null && isset($s->rhs) && $s->rhs instanceof LeanArgsSpaceSeparated) {
            $args = $s->rhs->args;
            for ($i = count($args) - 1; $i >= 0; $i--) {
                if ($args[$i] instanceof LeanCaret) continue;
                return $args[$i] instanceof Lean_partial ? $args[$i] : null;
            }
        }
        if ($s instanceof Lean_int) {
            $innerPartial = $s->measurePartial();
            if (!$innerPartial) return null;
            $a = $innerPartial->arg;
            if ($a instanceof LeanArgsSpaceSeparated) {
                for ($i = count($a->args) - 1; $i >= 0; $i--) {
                    if ($a->args[$i] instanceof LeanCaret) continue;
                    return $a->args[$i] instanceof Lean_partial ? $a->args[$i] : null;
                }
            }
            return null;
        }
        return null;
    }

    /** Render the integrand, filtering out the measure partial. */
    private function integrandLatex(&$syntax = null, $partial = null)
    {
        if (!$partial) return $this->scope ? $this->scope->toLatex($syntax) : '';
        if ($this->scope instanceof LeanArgsSpaceSeparated) {
            $args = array_filter($this->scope->args, function ($a) use ($partial) {
                return $a !== $partial && !($a instanceof LeanCaret);
            });
            $args = array_values($args);
            return implode(' ', array_map(function ($a) use (&$syntax) {
                return $a->toLatex($syntax);
            }, $args));
        }
        // Binary operator scope (e.g. `c • f x ∂μ`): partial is in scope.rhs
        if ($this->scope !== null && isset($this->scope->rhs) && $this->scope->rhs instanceof LeanArgsSpaceSeparated &&
            in_array($partial, $this->scope->rhs->args, true)) {
            $filteredRhs = array_filter($this->scope->rhs->args, function ($a) use ($partial) {
                return $a !== $partial && !($a instanceof LeanCaret);
            });
            $filteredRhs = array_values($filteredRhs);
            $lhsLatex = $this->scope->lhs->toLatex($syntax);
            $rhsLatex = implode(' ', array_map(function ($a) use (&$syntax) {
                return $a->toLatex($syntax);
            }, $filteredRhs));
            $op = $this->scope->command ?? $this->scope->operator;
            return "{$lhsLatex} {$op} {$rhsLatex}";
        }
        return $this->scope->toLatex($syntax);
    }

    // Standard math notation: \int\limits_a^b f(x)\,\mathrm{d}x
    // (cf. SymPy LatexPrinter._print_Integral).
    public function latexFormat()
    {
        $partial = $this->measurePartial();
        $diff = $partial ? '\\partial' : '\\mathrm{d}';
        $tail = "{\\color{blue}{$diff}}{%s}";
        $dom = $this->intDomain();
        if ($dom instanceof LeanUpto)
            return "\\int\\limits_{%s}^{%s} %s\\, {$tail}";
        if ($dom !== null)
            return "\\int\\limits_{%s} %s\\, {$tail}";
        return "\\int %s\\, {$tail}";
    }

    public function latexArgs(&$syntax = null)
    {
        $partial = $this->measurePartial();
        $body = $this->integrandLatex($syntax, $partial);
        $colon = $this->binderColon();
        $x = $colon ? $colon->lhs->toLatex($syntax) : '';
        $tail = $x ?: ($partial ? $partial->bound->toLatex($syntax) : '');
        $dom = $this->intDomain();
        if ($dom instanceof LeanUpto)
            return [$dom->lhs->toLatex($syntax), $dom->rhs->toLatex($syntax), $body, $tail];
        if ($dom !== null)
            return [$dom->toLatex($syntax), $body, $tail];
        return [$body, $tail];
    }
}

/**
 * `∂[x] body` / measure `∂μ`. Bound+scope like ∑/lim; path Deriv.
 */
class Lean_partial extends LeanBigOperator
{
    public static $input_priority = 75;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∂';
            case 'command':
                return '\\partial';
            case 'stack_priority':
                if ($this->scope)
                    return LeanAdd::$input_priority;
                if (!($this->bound instanceof LeanCaret))
                    return 67;
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        if ($this->parent)
            return $this->parent->insert_comma($this);
        throw new Exception(__METHOD__ . ' is unexpected for ' . get_class($this));
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->bound->set_line($line);
        if (!$this->scope)
            return $line;
        $s = $this->sep();
        if ($s && $s[0] === "\n")
            $line++;
        return $this->scope->set_line($line);
    }

    public function strFormat()
    {
        if (!$this->scope)
            return "$this->operator%s";
        return "$this->operator[%s]" . $this->sep() . "%s";
    }

    public function derivSugar()
    {
        if (!$this->scope)
            return null;
        $index = $this->bound;
        if ($this->scope instanceof LeanArgsSpaceSeparated)
            $body = array_values(array_filter($this->scope->args, fn($a) => !($a instanceof LeanCaret)));
        else if ($this->scope instanceof LeanCaret)
            $body = [];
        else
            $body = [$this->scope];
        if ($index instanceof LeanEq && $index->lhs instanceof LeanToken)
            return ['name' => $index->lhs, 'point' => $index->rhs, 'body' => $body];
        return ['name' => $index, 'point' => null, 'body' => $body];
    }

    public function latexArgs(&$syntax = null)
    {
        $sugar = $this->derivSugar();
        if (!$sugar)
            return [$this->bound->toLatex($syntax)];
        $body = [];
        foreach ($sugar['body'] as $a) {
            if ($a instanceof LeanParenthesis && $a->arg instanceof LeanDiv)
                $a = $a->arg;
            $body[] = $a->toLatex($syntax);
        }
        $name = $sugar['name']->toLatex($syntax);
        if (!$sugar['point'])
            return $body ? array_merge([$name], $body) : [$name];
        $point = $sugar['point'];
        if ($point instanceof LeanParenthesis)
            $point = $point->arg;
        return array_merge([$name], $body, [$name, $point->toLatex($syntax)]);
    }

    public function latexFormat()
    {
        $sugar = $this->derivSugar();
        if (!$sugar)
            return '\\partial{%s}';
        $body = implode('\\ ', array_map(fn() => '{%s}', $sugar['body']));
        $partial = $body ? "\\partial_{%s} {" . $body . "}" : '\\partial_{%s}';
        if (!$sugar['point'])
            return $partial;
        return "\\left. " . $partial . " \\right|_{{%s} = {%s}}";
    }

    public function holeRegex($opts = [])
    {
        return ($this->bound !== null || $this->scope !== null) ? "Deriv_" : null;
    }

}

/**
 * `∇[θ] body` / binder-free `∇ J` / `∇ J θ`. Bound+scope like lim/∂.
 */
class Lean_nabla extends LeanBigOperator
{
    public static $input_priority = 75;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∇';
            case 'command':
                return '\\nabla';
            case 'stack_priority':
                if ($this->scope)
                    return LeanAdd::$input_priority;
                if (!($this->bound instanceof LeanCaret))
                    return 67;
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        if ($this->parent)
            return $this->parent->insert_comma($this);
        throw new Exception(__METHOD__ . ' is unexpected for ' . get_class($this));
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->bound->set_line($line);
        if (!$this->scope)
            return $line;
        $s = $this->sep();
        if ($s && $s[0] === "\n")
            $line++;
        return $this->scope->set_line($line);
    }

    public function strFormat()
    {
        if ($this->scope)
            return "$this->operator[%s]" . $this->sep() . "%s";
        return "$this->operator %s";
    }

    public function nablaSugar()
    {
        if ($this->scope) {
            $index = $this->bound;
            if ($this->scope instanceof LeanArgsSpaceSeparated)
                $body = array_values(array_filter($this->scope->args, fn($a) => !($a instanceof LeanCaret)));
            else if ($this->scope instanceof LeanCaret)
                $body = [];
            else
                $body = [$this->scope];
            if ($index instanceof LeanEq && $index->lhs instanceof LeanToken)
                return ['kind' => 'binder', 'name' => $index->lhs, 'point' => $index->rhs, 'body' => $body];
            return ['kind' => 'binder', 'name' => $index, 'point' => null, 'body' => $body];
        }
        $b = $this->bound;
        if ($b instanceof LeanCaret)
            return null;
        if ($b instanceof LeanArgsSpaceSeparated)
            return ['kind' => 'function', 'operands' => array_values(array_filter($b->args, fn($a) => !($a instanceof LeanCaret)))];
        return ['kind' => 'function', 'operands' => [$b]];
    }

    public function latexArgs(&$syntax = null)
    {
        $sugar = $this->nablaSugar();
        if (!$sugar)
            return [$this->bound->toLatex($syntax)];
        if ($sugar['kind'] === 'function') {
            $out = [];
            foreach ($sugar['operands'] as $arg) {
                if ($arg instanceof LeanParenthesis && $arg->arg instanceof LeanDiv)
                    $arg = $arg->arg;
                if ($arg instanceof LeanParenthesis)
                    $arg = $arg->arg;
                $out[] = $arg->toLatex($syntax);
            }
            return $out;
        }
        $body = [];
        foreach ($sugar['body'] as $a) {
            if ($a instanceof LeanParenthesis && $a->arg instanceof LeanDiv)
                $a = $a->arg;
            $body[] = $a->toLatex($syntax);
        }
        $name = $sugar['name']->toLatex($syntax);
        if (!$sugar['point'])
            return $body ? array_merge([$name], $body) : [$name];
        $point = $sugar['point'];
        if ($point instanceof LeanParenthesis)
            $point = $point->arg;
        return array_merge([$name], $body, [$name, $point->toLatex($syntax)]);
    }

    public function latexFormat()
    {
        $sugar = $this->nablaSugar();
        if (!$sugar)
            return '\\nabla {%s}';
        if ($sugar['kind'] === 'function') {
            $ops = $sugar['operands'];
            if (count($ops) === 1)
                return '\\nabla {%s}';
            $rest = implode('\\ ', array_map(fn() => '{%s}', array_slice($ops, 1)));
            return "\\nabla {%s}\\left($rest\\right)";
        }
        $body = implode('\\ ', array_map(fn() => '{%s}', $sugar['body']));
        $nabla = $body ? "\\nabla_{%s} {" . $body . "}" : '\\nabla_{%s}';
        if (!$sugar['point'])
            return $nabla;
        return "\\left. " . $nabla . " \\right|_{{%s} = {%s}}";
    }

    public function holeRegex($opts = [])
    {
        return ($this->bound !== null || $this->scope !== null) ? "Grad_" : null;
    }

}



/**
 * Random big-ops: `𝔼[binder](body)`, `ℙ[π](event)` / `ℙ[π]{event}`, `𝕍𝕒𝕣[binder](body)`.
 * Promoted from GetElem + Parenthesis/Brace (bound/scope like ∑/∂/∇).
 * Mathlib `Var[Y]` stays plain GetElem.
 */
class LeanRandomBigOp extends LeanBigOperator
{
    public static $input_priority = 67;
    /** @var string */
    public $bodyDelim = 'paren';

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->scope)
                    return LeanAdd::$input_priority;
                return 67;
            case 'pathToken':
                return 'Expect';
            default:
                return parent::__get($vname);
        }
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->bound->set_line($line);
        if (!$this->scope)
            return $line;
        return $this->scope->set_line($line);
    }

    public function strFormat()
    {
        if (!$this->scope)
            return "$this->operator[%s]";
        return "$this->operator[%s]%s";
    }

    public function sep()
    {
        return '';
    }

    public function binderLatex(&$syntax = null)
    {
        $ix = $this->bound;
        if ($ix instanceof LeanColon) {
            $ty = $ix->rhs;
            if ($ty instanceof LeanParenthesis)
                $ty = $ty->arg;
            if ($ty instanceof LeanBitOr)
                return '{' . $ix->lhs->toLatex($syntax) . '} : {' . $ty->lhs->toLatex($syntax) . '}';
        }
        return $ix->toLatex($syntax);
    }

    public function latexArgs(&$syntax = null)
    {
        $binder = $this->binderLatex($syntax);
        if (!$this->scope)
            return [$binder];
        return [$binder, $this->scope->toLatex($syntax)];
    }

    /**
     * Promote GetElem(𝔼|ℙ|𝕍𝕒𝕣, binder) + closed Parenthesis/Brace → Lean_* bigop.
     * @param LeanPairedGroup $bodyDelim
     * @return Lean|null
     */
    public static function tryPromote($bodyDelim)
    {
        $p = $bodyDelim->parent;
        if (!($p instanceof LeanArgsSpaceSeparated))
            return null;
        $i = array_search($bodyDelim, $p->args, true);
        if ($i === false || $i <= 0)
            return null;
        $head = $p->args[$i - 1];
        if (!($head instanceof LeanGetElem))
            return null;
        $base = $head->lhs ?? $head->args[0] ?? null;
        if (!($base instanceof LeanToken))
            return null;
        $Ctor = null;
        if ($base->text === '𝔼')
            $Ctor = Lean_Expect::class;
        else if ($base->text === 'ℙ')
            $Ctor = Lean_Prob::class;
        else if ($base->text === '𝕍𝕒𝕣')
            $Ctor = Lean_Var::class;
        if (!$Ctor)
            return null;
        $binder = $head->rhs ?? $head->args[1] ?? null;
        $node = new $Ctor($binder, $bodyDelim->indent, $bodyDelim->level, $p);
        $node->scope = $bodyDelim;
        $node->bodyDelim = $bodyDelim instanceof LeanBrace ? 'brace' : 'paren';
        array_splice($p->args, $i - 1, 2, [$node]);
        $bodyDelim->parent = $node;
        if ($binder)
            $binder->parent = $node;
        if (count($p->args) === 1 && $p->parent) {
            $node->parent = null;
            $p->parent->replace($p, $node);
            return $node;
        }
        $node->parent = $p;
        return $node;
    }
}

class Lean_Expect extends LeanRandomBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return '𝔼';
            case 'pathToken':
                return 'Expect';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\mathop{{𝔼}}\\limits_{%s}';
        return '\\mathop{{𝔼}}\\limits_{%s}\\ {%s}';
    }
}

class Lean_Prob extends LeanRandomBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'ℙ';
            case 'pathToken':
                return 'Prob';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '{{ℙ}}_{%s}';
        return '{{{ℙ}}_{%s}}\\ {%s}';
    }
}

class Lean_Var extends LeanRandomBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return '𝕍𝕒𝕣';
            case 'pathToken':
                return 'Var';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '{{𝕍𝕒𝕣}}_{%s}';
        return '{{{𝕍𝕒𝕣}}_{%s}}\\ {%s}';
    }
}


/**
 * Limits-style GetElem sugars: max/min/sup/inf/max⁻¹/min⁻¹[binder] body.
 * Promoted from GetElem + body (paren/brace or SpaceSeparated juxta).
 * Unicode ⨅/⨆ stay LeanInf/LeanSup when present in JS; not these classes.
 */
class LeanLimitsBigOp extends LeanBigOperator
{
    public static $input_priority = 67;

    /** @var array<string,class-string>|null */
    public static $LIMITS_CTOR = null;

    public static function limitsCtorFor($text)
    {
        $map = self::$LIMITS_CTOR;
        return $map[$text] ?? null;
    }

    public static function isLimitsGetElem($head)
    {
        if (!($head instanceof LeanGetElem))
            return null;
        $base = $head->lhs ?? $head->args[0] ?? null;
        if (!($base instanceof LeanToken))
            return null;
        $Ctor = self::limitsCtorFor($base->text);
        if (!$Ctor)
            return null;
        return [
            'Ctor' => $Ctor,
            'binder' => $head->rhs ?? $head->args[1] ?? null,
            'base' => $base,
        ];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->scope)
                    return LeanAdd::$input_priority;
                return 67;
            case 'pathToken':
                return 'Max';
            default:
                return parent::__get($vname);
        }
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->bound->set_line($line);
        if (!$this->scope)
            return $line;
        $s = $this->sep();
        if ($s && $s[0] === "\n")
            ++$line;
        return $this->scope->set_line($line);
    }

    public function strFormat()
    {
        if (!$this->scope)
            return "$this->operator[%s]";
        return "$this->operator[%s] %s";
    }

    public function sep()
    {
        return ' ';
    }

    public function binderLatex(&$syntax = null)
    {
        // Mirror JS LeanGetElem::expectBinderIndexLatex
        $ix = $this->bound;
        if ($ix instanceof LeanColon) {
            $ty = $ix->rhs;
            if ($ty instanceof LeanParenthesis)
                $ty = $ty->arg;
            if ($ty instanceof LeanBitOr)
                return '{' . $ix->lhs->toLatex($syntax) . '} : {' . $ty->lhs->toLatex($syntax) . '}';
        }
        return $ix->toLatex($syntax);
    }

    public function latexArgs(&$syntax = null)
    {
        $binder = $this->binderLatex($syntax);
        if (!$this->scope)
            return [$binder];
        return [$binder, $this->scope->toLatex($syntax)];
    }

    /**
     * @param LeanArgsSpaceSeparated $ss
     * @return Lean|null
     */
    public static function tryPromoteSpaceSeparated($ss)
    {
        if (!($ss instanceof LeanArgsSpaceSeparated) || count($ss->args) < 2)
            return null;
        $info = self::isLimitsGetElem($ss->args[0]);
        if (!$info)
            return null;
        $rest = array_slice($ss->args, 1);
        $scope = count($rest) === 1
            ? $rest[0]
            : new LeanArgsSpaceSeparated($rest, $ss->indent, $ss->level);
        $Ctor = $info['Ctor'];
        $node = new $Ctor($info['binder'], $ss->indent, $ss->level, $ss->parent);
        $node->scope = $scope;
        if ($info['binder'])
            $info['binder']->parent = $node;
        if ($scope)
            $scope->parent = $node;
        if ($ss->parent) {
            $node->parent = null;
            $ss->parent->replace($ss, $node);
        } else {
            $node->parent = null;
        }
        return $node;
    }

    /**
     * @param LeanPairedGroup $bodyDelim
     * @return Lean|null
     */
    public static function tryPromote($bodyDelim)
    {
        $p = $bodyDelim->parent;
        if (!($p instanceof LeanArgsSpaceSeparated))
            return null;
        $i = array_search($bodyDelim, $p->args, true);
        if ($i === false || $i <= 0)
            return null;
        $head = $p->args[$i - 1];
        $info = self::isLimitsGetElem($head);
        if (!$info)
            return null;
        $Ctor = $info['Ctor'];
        $node = new $Ctor($info['binder'], $bodyDelim->indent, $bodyDelim->level, $p);
        $node->scope = $bodyDelim;
        array_splice($p->args, $i - 1, 2, [$node]);
        $bodyDelim->parent = $node;
        if ($info['binder'])
            $info['binder']->parent = $node;
        if (count($p->args) === 1 && $p->parent) {
            $node->parent = null;
            $p->parent->replace($p, $node);
            return $node;
        }
        $node->parent = $p;
        return $node;
    }
}

class Lean_max extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'max';
            case 'pathToken':
                return 'Max';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\max\\limits_{%s}';
        return '\\max\\limits_{%s} {%s}';
    }
}

class Lean_min extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'min';
            case 'pathToken':
                return 'Min';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\min\\limits_{%s}';
        return '\\min\\limits_{%s} {%s}';
    }
}

class Lean_sup extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'sup';
            case 'pathToken':
                return 'Sup';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\sup\\limits_{%s}';
        return '\\sup\\limits_{%s} {%s}';
    }
}

class Lean_inf extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'inf';
            case 'pathToken':
                return 'Inf';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\inf\\limits_{%s}';
        return '\\inf\\limits_{%s} {%s}';
    }
}

class Lean_argmax extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'max⁻¹';
            case 'pathToken':
                return 'ArgMax';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\underset{%s}{\\operatorname{max}^{-1}}';
        return '\\underset{%s}{\\operatorname{max}^{-1}} {%s}';
    }
}

class Lean_argmin extends LeanLimitsBigOp
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'baseOperator':
                return 'min⁻¹';
            case 'pathToken':
                return 'ArgMin';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        if (!$this->scope)
            return '\\underset{%s}{\\operatorname{min}^{-1}}';
        return '\\underset{%s}{\\operatorname{min}^{-1}} {%s}';
    }
}

LeanLimitsBigOp::$LIMITS_CTOR = [
    'max' => Lean_max::class,
    'min' => Lean_min::class,
    'sup' => Lean_sup::class,
    'inf' => Lean_inf::class,
    'max⁻¹' => Lean_argmax::class,
    'min⁻¹' => Lean_argmin::class,
];


class Lean_bigcap extends LeanBigOperator
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⋂';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bigcup extends LeanBigOperator
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⋃';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanStack extends LeanBigOperator
{
    public static $input_priority = 52;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'Stack';
            case 'command':
                return 'Stack';
            case 'stack_priority':
                return 28;
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax[get_class($this)] = true;
        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        return "\left[{%s}\\right]{%s}";
    }

    public function push_args_indented($indent, $newline_count, $function_call = true) {
    }
    public function strFormat()
    {
        return "[%s] %s";
    }

}

// END OF big operator family (LeanParser stays in lean.php)
