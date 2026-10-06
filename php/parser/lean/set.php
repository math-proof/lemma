<?php
/**
 * Set operators and inclusion (`LeanSetOperator`, \\, ∪, ∩, ⊆, ⊂, ⊇, ⊃).
 *
 * Loaded by lean.php after LeanLogic is declared (⊇ / ⊃ extend LeanLogic).
 * Mirrors static/js/parser/lean/set.js. Not a standalone entry point.
 */

abstract class LeanSetOperator extends LeanBinary {
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }
}

class Lean_setminus extends LeanSetOperator
{
    public static $input_priority = 70;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return "\\";
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_cup extends LeanSetOperator
{
    public static $input_priority = 65;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∪';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_cap extends LeanSetOperator
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∩';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_subseteq extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊆';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_subset extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊂';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_supseteq extends LeanLogic
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊇';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_supset extends LeanLogic
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊃';
            default:
                return parent::__get($vname);
        }
    }
}
