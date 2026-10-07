<?php
/**
 * Assignment `:=` (`LeanAssign`).
 *
 * Loaded by lean.php after `colon.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/assign.js. PHP `echo`, `insert`,
 * `insert_newline`, `is_indented`, and `sep` stay shorter than the JS
 * methods. Not a standalone entry point.
 */

class LeanAssign extends LeanBinary
{
    public static $input_priority = 18;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return ':=';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->rhs->echo();
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->rhs) {
                if ($caret instanceof LeanCaret) {
                    $caret->indent = $indent;
                    $this->rhs = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
                    $caret = $this->rhs->push_newlines($newline_count - 1);
                } elseif ($caret instanceof LeanArgsNewLineSeparated) {
                    if ($this->parent)
                        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
                } else {
                    if ($this->parent instanceof LeanCalc)
                        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
                    // first field of `{ a := 1⏎ b := 2 }` / `{ s with a := 1⏎ b := 2 }`: the brace / `with` opens the
                    // structure-instance body (mirrors assign.js). A deeper line after a field continues its value.
                    $p = $this->parent;
                    $owner = $p instanceof LeanBrace ? $p : ($p instanceof LeanWith && $p->isStructUpdate() ? $p : null);
                    $brace = $owner instanceof LeanWith ? $owner->parent->parent : $owner;
                    if ($brace && $brace->indent < $indent)
                        return $owner->insert_newline($this, $newline_count, $indent, $next);
                    $caret = $this->push_args_indented($indent, $newline_count, false);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $type)
    {
        return $this->insert_word($caret, $type);
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return !$parent || $parent instanceof LeanArgsNewLineSeparated || ($parent instanceof LeanArgsIndented && $parent->rhs === $this) ||
            // a field of a structure-instance body
            ($parent instanceof LeanStatements && $parent->structInst === true);
    }

    public function relocate_last_comment()
    {
        $rhs = $this->rhs;
        $rhs->relocate_last_comment();
    }

    public function sep()
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LeanArgsNewLineSeparated) {
            $lines = $rhs->args;
            if (count($lines) > 2 || !($lines[1] ?? null instanceof LeanArgsNewLineSeparated) || $lines[0] ?? null instanceof LeanLineComment)
                return "\n";
        }
        return ' ';
    }
    public function split(&$syntax = null)
    {
        if (($by = $this->rhs) instanceof LeanBy && ($stmts = $by->arg) instanceof LeanStatements) {
            $self = clone $this;
            $self->rhs->arg = new LeanCaret($by->indent, $by->level);
            $statements[] = $self;
            $stmts->swap_echo_star($syntax, $statements);
            return $statements;
        }
        if (($calc = $this->rhs) instanceof LeanCalc) {
            if ($syntax !== null)
                $syntax['calc'] = true;
            $self = clone $this;
            $calc = $self->rhs;
            $statements = $calc->split($syntax);
            $calc->arg = new LeanCaret($calc->indent, $calc->level);
            $statements[0] = $self;
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

}

// END OF assign family (LeanParser stays in lean.php)
