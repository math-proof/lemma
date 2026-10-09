<?php
/**
 * Membership and iff (`Lean_in`, `Lean_notin`, `Lean_leftrightarrow`).
 *
 * Loaded by lean.php after LeanBinaryBoolean (and after relational.php).
 * Mirrors js/parser/lean/membership.js. Not a standalone entry point.
 */

class Lean_in extends LeanBinaryBoolean
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∈';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanParenthesis) {
            if (!($lhs->arg instanceof LeanColon))
                $lhs = $lhs->arg;
        }
        if ($rhs instanceof LeanParenthesis && $rhs->arg instanceof LeanIte)
            $rhs = $rhs->arg;
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class Lean_notin extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∉';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanParenthesis) {
            $lhs = $lhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class Lean_leftrightarrow extends LeanBinaryBoolean
{
    public static $input_priority = 20;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '↔';
            default:
                return parent::__get($vname);
        }
    }
}
