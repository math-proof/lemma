<?php
/**
 * Arrows (`LeanRightarrow`, `Lean_rightarrow`, `Lean_mapsto`, `Lean_leftarrow`).
 *
 * Loaded by lean.php after `LeanBar`. Extends `LeanBinary` / `LeanUnary`, which
 * already exist. Mirrors static/js/parser/lean/arrows.js. Not a standalone entry point.
 */

class LeanRightarrow extends LeanBinary
{
    public static $input_priority = 19; // same as LeanColon::$input_priority;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '=>';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $token = [];
        if (($parent = $this->parent) instanceof LeanBar && ($parent = $parent->parent) instanceof LeanWith && (($parent = $parent->parent) instanceof Lean_match || $parent instanceof LeanTactic && $parent->func == 'induction')) {
            $token[] = new LeanToken('⊢', $this->rhs->indent, $this->rhs->level);
            $subject = $parent->args[0];
            if ($subject instanceof LeanArgsCommaSeparated) {
                foreach ($subject->args as $sujet) {
                    if ($sujet instanceof LeanColon)
                        $token[] = $sujet->lhs;
                }
            } elseif ($subject instanceof LeanColon)
                $token[] = $subject->lhs;
        }
        $expr = $this->lhs;
        if ($expr instanceof LeanArgsSpaceSeparated) {
            if ($expr->args[0] instanceof LeanToken)
                $func = $expr->args[0]->text;
            elseif ($expr->args[0] instanceof LeanProperty && $expr->args[0]->lhs instanceof LeanCaret && $expr->args[0]->rhs instanceof LeanToken)
                $func = $expr->args[0]->rhs->text;
            else
                $func = null;
            switch ($func) {
                case 'succ':
                case 'ofNat':
                case 'negSucc':
                    $start = 2;
                    break;
                case 'cons':
                    $start = 3;
                    break;
                default:
                    $start = 1;
                    break;
            }
            array_push($token, ...array_slice($expr->args, $start));
        } elseif ($expr instanceof LeanAngleBracket) {
            if ($expr->arg instanceof LeanArgsCommaSeparated)
                // | ⟨v, property⟩ =>
                array_push($token, ...array_slice($expr->arg->args, 1));
        } elseif ($expr instanceof LeanArgsCommaSeparated) {
            // | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
            foreach ($expr->args as $arg) {
                if ($arg instanceof LeanAngleBracket && $arg->arg instanceof LeanArgsCommaSeparated)
                    $token[] = $arg->arg->args[1];
            }
        }

        $stmt = $this->rhs;
        $stmt->echo();
        if ($token && $stmt instanceof LeanStatements) {
            $indent = $stmt->args[0]->indent;
            $level = $stmt->args[0]->level;
            if (count($token) > 1)
                $token = new LeanArgsCommaSeparated(
                    array_map(
                        function ($arg) use ($indent, $level) {
                            $arg = clone $arg;
                            $arg->indent = $indent;
                            $arg->level = $level;
                            return $arg;
                        },
                        $token
                    ),
                    $indent, $level
                );
            else
                [$token] = $token;
            $stmt->unshift(new LeanTactic('echo', $token, $indent, $level));
        }
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent, $caret->level));
                return $caret;
            }
        }
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret === $this->rhs) {
            if ($caret instanceof LeanCaret || $caret instanceof LeanLineComment) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                    $caret->indent = $indent;
                    $this->rhs = new LeanStatements([$caret], $indent, $caret->level);
                    if (!($caret instanceof LeanCaret))
                        ++$newline_count;
                    for ($i = 1; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($indent, $caret->level);
                        $this->rhs->push($caret);
                    }
                    return $caret;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
    }

    public function relocate_last_comment()
    {
        $this->rhs->relocate_last_comment();
    }

    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ($this->rhs instanceof LeanCaret ? '' : ' ');
    }

    public function strFormat()
    {
        $sep = $this->sep();
        $lhs = "%s";
        if (!($this->lhs instanceof LeanCaret))
            $lhs .= ' ';
        return "$lhs$this->operator$sep%s";
    }

}

class Lean_rightarrow extends LeanBinary
{
    public static $input_priority = 25; // right associative operator
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 24;
            case 'operator':
                return '→';
            default:
                return parent::__get($vname);
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        [$lhs, $rhs] = $this->args;
        if (($rhs instanceof LeanToken && in_array($rhs->text, ['0', '∞'], true)) ||
            (($rhs instanceof LeanPlus || $rhs instanceof LeanNeg) && $rhs->arg instanceof LeanToken && $rhs->arg->text === '∞') ||
            (($rhs instanceof LeanPosPart || $rhs instanceof LeanNegPart) && $rhs->arg instanceof LeanToken && $rhs->arg->text === '0'))
            return true;
        return ($lhs instanceof LeanToken && (($vars["$lhs"] ?? 'Prop') == 'Prop') || $lhs->isProp($vars)) &&
            ($rhs instanceof LeanToken && (($vars["$rhs"] ?? 'Prop') == 'Prop') || $rhs->isProp($vars));
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

class Lean_mapsto extends LeanBinary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 23;
            case 'operator':
                return '↦';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
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

class Lean_leftarrow extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '←';
            default:
                return parent::__get($vname);
        }
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

// END OF arrows family (LeanArgsSpaceSeparated stays in lean.php)
