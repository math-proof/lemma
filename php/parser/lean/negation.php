<?php
/**
 * Negation (`Lean_lnot`, `LeanNot`).
 *
 * Loaded by lean.php after `arrows.php`. Extends `LeanUnary` and uses `LeanProp`,
 * which already exist. Mirrors static/js/parser/lean/negation.js. Not a standalone entry point.
 */

class Lean_lnot extends LeanUnary
{
    public static $input_priority = 40;
    use LeanProp;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '¬';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

}

class LeanNot extends LeanUnary
{
    public static $input_priority = 40;
    use LeanProp;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '!';
            case 'command':
                return '\text{!}';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

}

// END OF negation family (LeanArgsSpaceSeparated stays in lean.php)
