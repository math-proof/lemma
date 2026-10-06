<?php
/**
 * Relational comparisons (`LeanRelational` and >, <, ≥, ≤, =, ==, !=, ≠, ≡, ≢, ≃, ≈, ≍, ∣).
 *
 * Also the PHP-only `=ᵐ` / independence nodes (`LeanMEq`, `LeanIndep`) and
 * `try_marginal_density_latex`, which only serves `LeanMEq`.
 * PHP `Lean_ll` / `Lean_gg` stay in arithmetic.php (they extend LeanArithmetic).
 * Loaded by lean.php after LeanBinaryBoolean. Mirrors static/js/parser/lean/relational.js.
 * Not a standalone entry point.
 */

abstract class LeanRelational extends LeanBinaryBoolean
{
    public static $input_priority = 50;
    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->strip_parenthesis();
        return [$lhs->toLatex($syntax), $rhs->toLatex($syntax)];
    }

}


class Lean_gt extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '>';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_ge extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≥';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_lt extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '<';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_le extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≤';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanEq extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '=';
            default:
                return parent::__get($vname);
        }
    }
}

/**
 * Detect the marginal-density pattern and render clean LaTeX (mirror of the
 * JS `tryMarginalDensityLatex`):
 *   (fun b ↦ lintegral μ (fun a ↦ ...density/rnDeriv... (a, b))) =ᵐ[ν]
 *     (Measure.map y ℙ).rnDeriv ν
 * →  ∫ 𝕡(x, 𝕪) dx =^m 𝕡(𝕪)   (sympy-style; density may be implicit via rnDeriv)
 * @return string[]|null [lhsLatex, rhsLatex] or null if pattern doesn't match
 */
function try_marginal_density_latex($lhs, $rhs)
{
    // LHS must be: fun b ↦ lintegral μ (fun a ↦ ... (a, b))
    if (!($lhs instanceof Lean_fun) || !($lhs->arg instanceof Lean_mapsto))
        return null;
    $lhsBody = $lhs->arg->rhs->peelGroup();
    if (!$lhsBody->headIs('lintegral'))
        return null;
    // lintegral args: [lintegral, μ, (fun a ↦ ...)]
    $lintegralArgs = $lhsBody->args;
    if (!is_array($lintegralArgs) || count($lintegralArgs) < 3)
        return null;
    $innerFun = $lintegralArgs[2]->peelGroup();
    if (!($innerFun instanceof Lean_fun) || !($innerFun->arg instanceof Lean_mapsto))
        return null;
    // Inner body: p (a, b)  OR  (...rnDeriv/density...) (a, b)
    $innerBody = $innerFun->arg->rhs->peelGroup();
    $innerStr = (string)$innerBody;
    $impliedPdf = str_contains($innerStr, 'rnDeriv') || str_contains($innerStr, 'density');
    if (!($innerBody instanceof LeanArgsSpaceSeparated))
        return null;
    $jointArgs = $innerBody->args;
    if (count($jointArgs) < 2)
        return null;
    // KaTeX_AMS lacks a blackboard lowercase-p glyph (`\mathbb{p}` falls back to
    // serif italic p), so emit the Unicode char — it renders as true 𝕡.
    $densityName = $impliedPdf ? '𝕡' : trim((string)$jointArgs[0]);
    // last arg is the pair (a, b): value b is a bare token (scalar level, not y ω)
    $pairArg = $jointArgs[count($jointArgs) - 1]->peelGroup();
    if (!($pairArg instanceof LeanArgsCommaSeparated) && !($pairArg instanceof LeanArgsSpaceSeparated))
        return null;
    $valueArgs = $pairArg->args;
    if (count($valueArgs) !== 2 || !($valueArgs[1] instanceof LeanToken))
        return null;

    // RHS: (Measure.map y ℙ).rnDeriv ν — a scalar pdf, not a fun; extract the random variable
    $rhsNode = $rhs;
    while ($rhsNode instanceof LeanStatements && count($rhsNode->args) > 0)
        $rhsNode = $rhsNode->args[0];
    while ($rhsNode instanceof LeanParenthesis)
        $rhsNode = $rhsNode->arg;
    $rhsStr = (string)$rhsNode;
    if (!str_contains($rhsStr, 'rnDeriv'))
        return null;
    if (!preg_match('/Measure\.map\s+([a-z])\s/', $rhsStr, $m))
        return null;
    $rvName = $m[1];

    // Build clean LaTeX — random variables highlighted red, matching the site convention.
    // `𝕡(x, y)` reads as the event `𝕡(x = x' ∧ y = y')`: slots inside 𝕡(·) name random
    // variables (red), while the `x` in `dx` is the bound integration dummy x' (black).
    $rv = "{\\color{red} {$rvName}}";
    return [
        "\\int {$densityName}({\\color{red} {x}}, {$rv})\\,dx",
        "{$densityName}({$rv})",
    ];
}

class LeanMEq extends LeanRelational
{
    // The parsed `modifier` is retained for echo output (`strFormat` must emit `=ᵐ[ν]`,
    // the only notation Mathlib knows) and for marginal-density recognition, but display
    // drops it entirely: the operator glyph and LaTeX command are plain `=ᵐ` / `=^{\mathrm{m}}`.
    public $modifier = '';

    private function latexOp(): string
    {
        return "=^{\\mathrm{m}}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '=ᵐ';
            case 'command':
                return $this->latexOp();
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax['=ᵐ'] = true;
        [$lhs, $rhs] = $this->strip_parenthesis();
        $pretty = try_marginal_density_latex($lhs, $rhs);
        if ($pretty !== null)
            return $pretty;
        return parent::latexArgs($syntax);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s =ᵐ[{$this->modifier}]{$sep}%s";
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "{%s} {$this->latexOp()}{$sep}{%s}";
    }
}

/** `x ⟂ᵢ[𝕡] y` — independence; the bracketed measure is kept for echo but elided in LaTeX. */
class LeanIndep extends LeanRelational
{
    // The parsed `modifier` is retained for echo output (`strFormat` must emit `⟂ᵢ[𝕡]`,
    // the only notation Mathlib knows), but display drops it entirely, like `=ᵐ[ν]`.
    public $modifier = '';

    private function latexOp(): string
    {
        return '⟂_{i}';
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⟂ᵢ';
            case 'command':
                return $this->latexOp();
            default:
                return parent::__get($vname);
        }
    }

    /**
     * The `⟂ᵢ` node a CondIndep `| Z` attaches to: $n itself, or the only line of a one-line
     * block (a `∀ …,` body starting on a new line) — mirrors JS `Lean_perp.independenceOf`.
     */
    public static function independenceOf($n)
    {
        while ($n instanceof LeanArgsNewLineSeparated && count($n->args) === 1) $n = $n->args[0];
        return $n instanceof LeanIndep ? $n : null;
    }

    /**
     * Colour a random-variable operand of `⟂ᵢ` red, head only (`Lean::headTokens`): `r[t + 1:]` → `r`,
     * `(s t, a t)` → `s`, `a`; indices and arguments stay black (mirrors JS `Lean_perp.markRandomVariableTerm`).
     */
    public static function markRandomVariableTerm($x)
    {
        foreach (Lean::headTokens($x) as $h) $h->setRandomVariable();
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax['⟂ᵢ'] = true;
        foreach ($this->args as $a) LeanIndep::markRandomVariableTerm($a);
        // keep a parenthesized pair rhs `(y, z)` intact — it is an argument, not grouping
        return array_map(
            function ($arg) use (&$syntax) {
                return $arg->toLatex($syntax);
            },
            $this->args
        );
    }

    /** Echo serialization keeps the bracketed measure (required by Lean's notation). */
    public function strFormat()
    {
        $sep = $this->sep();
        $op = $this->modifier !== '' ? "⟂ᵢ[{$this->modifier}]" : '⟂ᵢ';
        return "%s {$op}{$sep}%s";
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "{%s} {$this->latexOp()}{$sep}{%s}";
    }
}

class LeanBEq extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '=\!\!=';
            case 'operator':
                return '==';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bne extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '!=';
            case 'operator':
                return '!=';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_ne extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≠';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_equiv extends LeanRelational
{
    public static $input_priority = 32;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≡';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanNotEquiv extends LeanRelational
{
    public static $input_priority = 32;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\not\equiv';
            case 'operator':
                return '≢';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_simeq extends LeanRelational
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≃';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax['≃'] = true;
        return parent::latexArgs($syntax);
    }

}

class Lean_approx extends LeanRelational
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≈';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax['≈'] = true;
        return parent::latexArgs($syntax);
    }
}

class Lean_asymp extends LeanRelational
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≍';
            default:
                return parent::__get($vname);
        }
    }
    public function latexArgs(&$syntax = null)
    {
        $syntax['≍'] = true;
        return parent::latexArgs($syntax);
    }
}

class LeanDvd extends LeanRelational
{
    public static $input_priority = 50;  # infix[lr]?:\d+ *" *∣
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '{\color{red}{\ \\mid\ }}';
            case 'operator':
                return '∣';
            default:
                return parent::__get($vname);
        }
    }
}
