<?php
/**
 * Lambda binder head (`Lean_fun`, `fun` / `λ`).
 *
 * Loaded by lean.php after `decl.php`. Extends `LeanUnary`, which already
 * exists. Mirrors js/parser/lean/fun.js. Not a standalone entry point.
 */

class Lean_fun extends LeanUnary
{
    public static $input_priority = 18;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'fun';
            case 'command':
                return '\lambda';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsNewLineSeparated || $parent instanceof LeanStatements;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => $this->arg->jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        return "$this->command\\ %s";
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

// END OF fun family (LeanParser stays in lean.php)
