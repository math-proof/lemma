<?php
/**
 * Logic / boolean connectives (`LeanLogic` and &&, ||, ^^, ∨, ∧).
 *
 * Loaded by lean.php after LeanBinaryBoolean is declared.
 * Mirrors static/js/parser/lean/logic.js. Not a standalone entry point.
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

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        return [$this->func => [$lhs, $rhs]];
    }
}
