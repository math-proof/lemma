<?php
/**
 * Abstract argument bases (`LeanArgs`, `LeanUnary`, `LeanBinary`).
 *
 * Loaded by lean.php after `LeanMultipleLine` and before `paired.php`
 * (`LeanPairedGroup` extends `LeanUnary`). Mirrors
 * static/js/parser/lean/abstract.js. PHP keeps these classes `abstract`
 * (`LeanBinary::sep` stays abstract). Not a standalone entry point.
 */

abstract class LeanArgs extends Lean
{
    public static $input_priority = 47;
    public function __clone()
    {
        parent::__clone();
        $this->args = array_map(fn($arg) => clone $arg, $this->args);
        foreach ($this->args as $arg) {
            $arg->parent = $this;
        }
    }

    public function __construct($args, $indent, $level, $parent = null)
    {
        parent::__construct($indent, $level, $parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return "\\$this->func";
            case 'func':
                return preg_replace('/^Lean_?/', '', get_class($this));
            default:
                return parent::__get($vname);
        }
    }

    public function insert_calc($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanCalc($caret, $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $func)
    {
        if ($caret instanceof LeanCaret) {
            $this->replace($caret, new LeanTactic($func, $caret, $this->indent, $caret->level));
            return $caret;
        }
        return $this->insert_word($caret, $func);
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function push_args_indented($indent, $newline_count, $function_call = true) {
        $end = end($this->args);
        if (!$function_call || $end instanceof LeanToken || $end instanceof LeanProperty || $end instanceof LeanParenthesis) {
            $caret = new LeanCaret($indent, $end->level);
            $new = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
            $caret = $new->push_newlines($newline_count - 1);
            $this->replace($end, new LeanArgsIndented($end, $new, $this->indent, $caret->level));
            return $caret;
        }
    }
    public function regexp()
    {
        $func = ucfirst($this->func);
        $args = array_map(fn($arg) => [...$arg->regexp(), "_"], $this->args);
        $regexp = [];
        foreach (itertools\product($args) as $list) {
            $expr = implode("", $list);
            $regexp[] = "$func$expr";
        }
        return $regexp;
    }

    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line);
        }
        return $line;
    }

    public function strip_parenthesis()
    {
        return array_map(fn($arg) => $arg instanceof LeanParenthesis && !($arg->arg instanceof LeanMethodChaining || $arg->arg instanceof Lean_rightarrow || $arg->arg instanceof LeanColon) ? $arg->arg : $arg, $this->args);
    }

    public function traverse()
    {
        yield $this;
        foreach ($this->args as $arg) {
            if ($arg != null)
                yield from $arg->traverse();
        }
    }

}

# Frac|Abs|Norm|Length|Sign|Square|Sqrt|Floor|Ceil|Sin|Cos|Tan|Cot|Arg|Neg|Inv|Cast|Coe|Exp|Log|Val|Card|ToNat|Arccos|Arcsin|Arctan|Arccot|Re|Im|Succ
abstract class LeanUnary extends LeanArgs
{
    public static $input_priority = 47;
    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct([], $indent, $level, $parent);
        $this->arg = $arg;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'arg':
                return $this->args[0];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'arg':
                $this->args[0] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert_if($caret)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->arg = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function jsonSerialize(): mixed
    {
        return $this->arg->jsonSerialize();
    }

    public function replace($old, $new)
    {
        assert($this->arg === $old, new Exception("assert failed: public function replace(\$old, \$new)"));
        $this->arg = $new;
    }

}

abstract class LeanBinary extends LeanArgs
{
    public static $input_priority = 47;

    public function __construct($lhs, $rhs, $indent, $level, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'lhs':
                return $this->args[0];
            case 'rhs':
                return $this->args[1];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'lhs':
                $this->args[0] = $val;
                break;
            case 'rhs':
                $this->args[1] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert_if($caret)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->rhs = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $func)
    {
        // consider the case where `case` is a tactic within (LeanColon/LeanAdd):
        // (h : arg x + arg y ∈ Ioc (-Real.pi) Real.pi) :
        return $this->insert_word($caret, $func);
    }
    public function jsonSerialize(): mixed
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
    }

    public function latexFormat()
    {
        return "{%s} $this->command {%s}";
    }

    abstract public function sep();

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->lhs->set_line($line);
        $sep = $this->sep();
        if ($sep && $sep[0] == "\n")
            ++$line;
        return $this->rhs->set_line($line);
    }

}

// END OF abstract family (LeanProperty stays in lean.php)
