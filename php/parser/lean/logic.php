<?php
/**
 * Logic / boolean connectives (`LeanLogic` and &&, ||, ^^, ∨, ∧).
 *
 * Loaded by lean.php after LeanBinaryBoolean is declared.
 * Mirrors js/parser/lean/logic.js. Not a standalone entry point.
 */

abstract class LeanLogic extends LeanBinaryBoolean
{
    public $hanging_indentation;
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function sep()
    {
        return $this->hanging_indentation ? "\n" . str_repeat(' ', $this->rhs->indent) : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }
}


class LeanLogicAnd extends LeanLogic
{
    public static $input_priority = 37;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 50;
            case 'command':
                return '\&\&';
            case 'operator':
                return '&&';
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof Lean_land) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}


class LeanLogicOr extends LeanLogic
{
    public static $input_priority = 37;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 36;
            case 'command':
            case 'operator':
                return '||';
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof Lean_lor) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

class LeanLogicXor extends LeanLogic
{
    public static $input_priority = 33;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\^\^';
            case 'operator':
                return '^^';
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}


class Lean_lor extends LeanLogic
{
    public static $input_priority = 30;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 29;
            case 'operator':
                return '∨';
            default:
                return parent::__get($vname);
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->rhs && $caret instanceof LeanCaret) {
            if ($indent >= $this->indent) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $this->hanging_indentation = true;
                $caret->indent = $indent;
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        return [$this->func => [$lhs, $rhs]];
    }

}

/**
 * Display-only: flatten nested `∧` of plain `=` into an eq chain when sides connect
 * (`a = b ∧ b = c ∧ c = d` → `a = b = c = d`), matching JS `eqChainSides` / py And._latex.
 * @param Lean_land $land
 * @return array|null ordered side nodes, or null if not a pure connected eq chain
 */
function lean_eq_chain_sides(Lean_land $land)
{
    $flatten = function ($n) use (&$flatten) {
        while ($n instanceof LeanParenthesis)
            $n = $n->arg;
        if ($n instanceof Lean_land)
            return array_merge($flatten($n->lhs), $flatten($n->rhs));
        return [$n];
    };
    $parts = $flatten($land);
    if (count($parts) < 2)
        return null;
    $pairs = [];
    foreach ($parts as $p) {
        $n = $p;
        while ($n instanceof LeanParenthesis)
            $n = $n->arg;
        // Plain `=` only (no =ᵐ / =ᶠ superscripts).
        if (!($n instanceof LeanEq) || !empty($n->superscript))
            return null;
        $lhs = $n->lhs;
        $rhs = $n->rhs;
        while ($lhs instanceof LeanParenthesis)
            $lhs = $lhs->arg;
        while ($rhs instanceof LeanParenthesis)
            $rhs = $rhs->arg;
        $pairs[] = [$lhs, $rhs];
    }
    $child = [];
    $parent = [];
    $lastLhs = null;
    foreach ($pairs as [$lhs, $rhs]) {
        $lk = (string)$lhs;
        $rk = (string)$rhs;
        if (array_key_exists($lk, $child))
            return null;
        $child[$lk] = ['node' => $rhs, 'key' => $rk];
        if (array_key_exists($rk, $parent))
            return null;
        $parent[$rk] = ['node' => $lhs, 'key' => $lk];
        $lastLhs = ['node' => $lhs, 'key' => $lk];
    }
    if ($lastLhs === null)
        return null;
    $root = $lastLhs;
    while (array_key_exists($root['key'], $parent))
        $root = $parent[$root['key']];
    $children = [$root['node']];
    $nextKey = $root['key'];
    while (array_key_exists($nextKey, $child)) {
        $step = $child[$nextKey];
        $children[] = $step['node'];
        $nextKey = $step['key'];
    }
    if (count($children) !== count($pairs) + 1)
        return null;
    return $children;
}

class Lean_land extends LeanLogic
{
    public static $input_priority = 35;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 34;
            case 'operator':
                return '∧';

            default:
                return parent::__get($vname);
        }
    }

    /**
     * Display latex: collapse connected plain-eq ∧-chains (py And._latex / JS Lean_land::toLatex).
     */
    public function toLatex(&$syntax = null)
    {
        $sides = lean_eq_chain_sides($this);
        if ($sides !== null) {
            $parts = [];
            foreach ($sides as $s)
                $parts[] = '{' . $s->toLatex($syntax) . '}';
            return implode(' = ', $parts);
        }
        return parent::toLatex($syntax);
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        return [$this->func => [$lhs, $rhs]];
    }
}
