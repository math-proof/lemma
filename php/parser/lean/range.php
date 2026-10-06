<?php
/**
 * Interval notation `a..b` (`LeanUpto`).
 *
 * Loaded by lean.php after `paired.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/range.js. PHP `sep` stays empty and the
 * formats stay `%s..%s`. Not a standalone entry point.
 */

/**
 * Interval notation `a..b` used by `∫ x in a..b, f x` (Mathlib `notation3 "a".."b"`).
 * Binds looser than arithmetic/relational nodes, matching the term-level parsing of the bounds.
 */
class LeanUpto extends LeanBinary
{
    public static $input_priority = 49; // LeanRelational::$input_priority - 1

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '..';
            default:
                return parent::__get($vname);
        }
    }

    public function sep()
    {
        return '';
    }

    public function strFormat()
    {
        return '%s..%s';
    }

    public function latexFormat()
    {
        return '%s..%s';
    }
}

// END OF range family (LeanParser stays in lean.php)
