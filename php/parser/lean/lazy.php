<?php
/**
 * Lazy application `<|` (`Lean_lazy`).
 *
 * Loaded by lean.php after `arithmetic.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/lazy.js. PHP keeps `operator`, `sep`, and
 * `strFormat`; JS does not. Not a standalone entry point.
 */

/** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
class Lean_lazy extends LeanBinary
{
    public static $input_priority = 20;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                // below input_priority, so a following `<|` nests on the right
                return 19;
            case 'operator':
                return '<|';
            default:
                return parent::__get($vname);
        }
    }

    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s <|{$sep}%s";
    }
}

// END OF lazy family (Lean_is stays in lean.php)
