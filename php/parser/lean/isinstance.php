<?php
/**
 * Type tests `is` / `is not` (`Lean_is`, `Lean_is_not`).
 *
 * Loaded by lean.php after `indexing.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/isinstance.js. PHP `operator` and `command`
 * stay on `__get`. `LeanStatements` is defined later in lean.php and is
 * resolved when `is_indented` runs. Not a standalone entry point.
 */

class Lean_is extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'is';
            case 'command':
                return '{\color{blue}\text{is}}';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function latexFormat()
    {
        return "{%s}\\ $this->command\\ {%s}";
    }

    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

class Lean_is_not extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '{\color{blue}\text{is not}}';
            case 'operator':
                return 'is not';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

// END OF isinstance family (LeanBar stays in lean.php)
