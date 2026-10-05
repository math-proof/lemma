<?php
/**
 * Big operators (`∑`, `lim`, `∏`, `∫`, `⋂`, `⋃`, `Stack`).
 *
 * Loaded by lean.php after LeanBigOperator and quantifier.php.
 * JS also has `LeanInf` / `LeanSup` (`⨅` / `⨆`); this file does not.
 * Mirrors static/js/parser/lean/bigops.js. Not a standalone entry point.
 */

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
    public function latexFormat()
    {
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
        $tail = $x ?: ($partial ? $partial->arg->toLatex($syntax) : '');
        $dom = $this->intDomain();
        if ($dom instanceof LeanUpto)
            return [$dom->lhs->toLatex($syntax), $dom->rhs->toLatex($syntax), $body, $tail];
        if ($dom !== null)
            return [$dom->toLatex($syntax), $body, $tail];
        return [$body, $tail];
    }
}

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
