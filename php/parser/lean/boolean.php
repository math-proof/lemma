<?php
/**
 * Abstract boolean-valued binary base (`LeanBinaryBoolean`).
 *
 * Loaded by lean.php after the `LeanProp` trait and before `relational.php`.
 * Relational comparisons, membership, and logic connectives extend this.
 * Mirrors static/js/parser/lean/boolean.js. PHP stays `abstract` and
 * `insert_newline` / `is_indented` stay shorter than the JS methods.
 * Not a standalone entry point.
 */

abstract class LeanBinaryBoolean extends LeanBinary
{
    use LeanProp;

    public function append($new, $type)
    {
        $indent = $this->indent;
        $level = $this->level;
        $caret = new LeanCaret($indent, $level);
        if (is_string($new)) {
            $new = new $new($caret, $indent, $level);
            $this->rhs = new LeanArgsSpaceSeparated([$this->rhs, $new], $indent, $level);
            return $caret;
        } else {
            $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent, $level));
            return $new;
        }
    }

    public function insert_colon($caret)
    {
        if ($caret === $this->rhs) {
            $new = new LeanCaret($caret->indent, $caret->level);
            $this->parent->replace($this, new LeanColon($this, $new, $caret->indent, $caret->level));
            return $new;
        }
        return $caret->push_binary('LeanColon');
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->rhs === $caret && $indent > $this->indent) {
            if ($caret instanceof LeanCaret) {
                $caret->indent = $indent;
                $this->rhs = new LeanStatements([$caret], $indent, $caret->level);
                return $caret;
            }
            return $this->parent->push_args_indented($indent, $newline_count, false);
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

}

// END OF boolean family (LeanBar stays in lean.php)
