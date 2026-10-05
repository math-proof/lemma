<?php
/**
 * Top-level commands (`LeanCommand`, `import` / `open` / `set_option` / `namespace`).
 *
 * Loaded by lean.php after `module.php`. Mirrors static/js/parser/lean/command.js.
 * `append` still writes `$this->sql`. `open` stays `'open'` (JS may render
 * `open scoped`). Later classes (`LeanArgsSpaceSeparated`, …) are resolved
 * when methods run.
 * Not a standalone entry point.
 */

abstract class LeanCommand extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
        ];
    }
    public function latexFormat()
    {
        return "$this->command %s";
    }
    public function strFormat()
    {
        return "$this->operator %s";
    }

}

class Lean_import extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'import';

            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_open extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'open';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_set_option extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'set_option';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function echo()
    {
        $arg = &$this->arg;
        if ($arg instanceof LeanArgsSpaceSeparated) {
            $args = &$arg->args;
            if (count($args) == 2 && $args[0] instanceof LeanToken && $args[1] instanceof LeanToken) {
                $value = &$args[1]->text;
                if ($args[0]->text == 'maxHeartbeats')
                    $value = strval(intval($value) * 5);
            }
        }
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_namespace extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'namespace';
            default:
                return parent::__get($vname);
        }
    }
}

// END OF command family (LeanBar stays in lean.php)
