<?php
/**
 * Match (`Lean_match`).
 *
 * Loaded by lean.php after `negation.php`. Extends `LeanArgs`, which already
 * exists. Mirrors static/js/parser/lean/match.js. Not a standalone entry point.
 */

class Lean_match extends LeanArgs
{
    public function __construct($subject, $indent, $level, $parent = null)
    {
        parent::__construct([$subject], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority - 1;
            case 'subject':
                return $this->args[0];
            case 'with':
                return $this->args[1] ?? null;
            case 'operator':
                return 'match';
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'subject':
                $this->args[0] = $val;
                break;
            case 'with':
                $this->args[1] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert($caret, $func, $type)
    {
        if (!$this->with && $func == 'LeanWith') {
            $caret = new LeanCaret($this->indent, $caret->level);
            $with = new $func($caret, $this->indent, $caret->level);
            $this->with = $with;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->subject) {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->subject = new LeanArgsCommaSeparated([$this->subject, $caret], $this->indent, $caret->level);
            return $caret;
        }
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        return parent::insert_tactic($caret, $token);
    }

    public function is_indented()
    {
        return true;
    }

    public function isProp($vars)
    {
        $cases = $this->with->args;
        $case = $cases[0] ?? null;
        if ($case instanceof LeanBar) {
            $rightarrow = $case->arg;
            if ($rightarrow instanceof LeanRightarrow)
                return $rightarrow->rhs->isProp($vars);
        }
    }
    public function latexArgs(&$syntax = null)
    {
        $subject = $this->subject->toLatex($syntax);
        if ($this->with) {
            $cases = $this->with->args;
            return array_map(function ($arg) use ($subject, &$syntax) {
                $arg = $arg->arg;
                $type = $arg->lhs->toLatex($syntax);
                $value = $arg->rhs->toLatex($syntax);
                return "{{$value}} & {\\color{blue}\\text{if}}\\ \\: $subject\\ =\\ $type";
            }, $cases);
        }
        return [$subject];
    }

    public function latexFormat()
    {
        if ($this->with) {
            $cases = $this->with->args;
            $cases = implode("\\\\", array_fill(0, count($cases), "%s"));
            return "\\begin{cases} $cases \\end{cases}";
        }
        return "match\\ %s";
    }
    public function relocate_last_comment()
    {
        $with = $this->with;
        if ($with instanceof LeanWith)
            $with->relocate_last_comment();
    }

    public function split(&$syntax = null)
    {
        if ($with = $this->with) {
            $self = clone $this;
            $self->with->args = [];
            $statements[] = $self;
            foreach ($with->args as $stmt)
                array_push($statements, ...$stmt->split($syntax));
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        if ($this->with)
            return "$this->operator %s %s";
        return "$this->operator %s";
    }

}

// END OF match family (LeanBy stays in lean.php)
