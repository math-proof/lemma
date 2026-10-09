<?php
/**
 * Match and tactic bar (`LeanBar`, `|`).
 *
 * Loaded by lean.php after `command.php` and before `arrows.php`. Mirrors
 * js/parser/lean/bar.js. `is_indented` always returns true. There is
 * no `insert_bar`. `insert_comma` tests `end($this->args)`. `split` uses the
 * arrow's level. Later classes (`LeanRightarrow`, `LeanArgsCommaSeparated`,
 * …) are resolved when methods run.
 * Not a standalone entry point.
 */

class LeanBar extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                //must be >= LeanAssign::$input_priority
                return LeanAssign::$input_priority;
            case 'operator':
            case 'command':
                return '|';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function is_indented()
    {
        return true;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LeanRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LeanStatements) {
                $arrow->rhs = new LeanCaret($arrow->indent, $arrow->level);
                $stmts->swap_echo_star($syntax, $statements);
            }
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

// END OF bar family (LeanParser stays in lean.php)
