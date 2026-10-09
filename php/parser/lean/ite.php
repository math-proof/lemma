<?php
/**
 * If-then-else (`LeanIte`).
 *
 * Loaded by lean.php after `match.php`. Extends `LeanArgs`, which already
 * exists. Mirrors js/parser/lean/ite.js. Not a standalone entry point.
 */

class LeanIte extends LeanArgs
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 23;
            case 'if':
                return $this->args[0];
            case 'then':
                return $this->args[1] ?? null;
            case 'else':
                return $this->args[2] ?? null;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'if':
                $this->args[0] = $val;
                break;
            case 'then':
                $this->args[1] = $val;
                break;
            case 'else':
                $this->args[2] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function echo()
    {
        [$if, $then, $else] = $this->args;
        $token = null;
        if ($if instanceof LeanColon && ($token = $if->args[0]) instanceof LeanToken);
        if ($then)
            $this->echo_then($token);
        if ($else)
            $this->echo_else($token);
    }

    public function echo_else($token) {
        $part = $this->else;
        $part->echo();
        if ($token) {
            if ($part instanceof LeanIte)
                $this::echo_part($part->then, $token);
            else 
                $this::echo_part($part, $token);
        }
    }

    public function echo_then($token) {
        $part = $this->then;
        $part->echo();
        if ($token)
            $this::echo_part($part, $token);
    }
    public function insert_colon($caret)
    {
        if ($caret === $this->if) {
            $new = new LeanCaret($caret->indent, $caret->level);
            $this->replace($caret, new LeanColon($caret, $new, $caret->indent, $caret->level));
            return $new;
        }
        return $caret->push_binary('LeanColon');
    }

    public function insert_else($caret)
    {
        if (!$this->else) {
            $caret = new LeanCaret($this->indent + 2, $caret->level);
            $this->else = $caret;
            return $caret;
        }
        if ($this->parent)
            return $this->parent->insert_else($this);
    }

    public function insert_if($caret)
    {
        if ($caret instanceof LeanCaret) {
            if ($caret === $this->else) {
                $this->else = new LeanIte([$caret], $this->indent, $caret->level);
                return $caret;
            }
            if ($caret === $this->then) {
                if ($caret->indent < $this->indent + 2)
                    $caret->indent = $this->indent + 2;
                $this->then = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->then) {
            if ($caret instanceof LeanTactic || $caret instanceof Lean_let) {
                $stmt = new LeanStatements([$caret], $caret->indent, $caret->level);
                $this->then = $stmt;
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LeanCaret($caret->indent, $caret->level);
                    $stmt->push($caret);
                }
            }
            return $caret;
        }
        if ($caret === $this->else) {
            if ($caret instanceof LeanCaret)
                return $caret;
            if ($indent > $this->indent && ($caret instanceof LeanTactic || $caret instanceof Lean_let)) {
                $stmt = new LeanStatements([$caret], $caret->indent, $caret->level);
                $this->else = $stmt;
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LeanCaret($caret->indent, $caret->level);
                    $stmt->push($caret);
                }
                return $caret;
            }
        }
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $func)
    {
        if ($caret instanceof LeanCaret) {
            $this->replace($caret, new LeanTactic($func, $caret, $this->indent + 2, $caret->level));
            return $caret;
        }
        $new = new LeanCaret($this->indent + 2, $caret->level);
        $this->replace($caret, new LeanStatements([$caret, new LeanTactic($func, $new, $this->indent + 2, $caret->level)], $this->indent + 2, $caret->level));
        return $new;
    }

    public function insert_then($caret)
    {
        if (!$this->then) {
            $caret = new LeanCaret($this->indent + 2, $caret->level);
            $this->then = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function is_indented()
    {
        $parent = $this->parent;
        # in case that $parent->then is null, wherein the `then` part is the result of splitting 
        return !$parent || $parent instanceof LeanStatements || $parent instanceof LeanIte && (!($then = $parent->then) || $this === $then);
    }

    public function latexArgs(&$syntax = null)
    {
        $cases = [];
        $else = $this;
        while (true) {
            [$if, $then, $else] = $else->strip_parenthesis();
            $if = $if->toLatex($syntax);
            $then = $then->toLatex($syntax);
            $cases[] = "{{$then}} & {\\color{blue}\\text{if}}\\ $if ";

            if (!($else instanceof LeanIte))
                break;
        }

        $else = $else->toLatex($syntax);
        return array_merge($cases, [$else]);
    }

    public function latexFormat()
    {
        $cases = 0;
        $else = $this;
        while (true) {
            [$if, $then, $else] = $else->strip_parenthesis();
            ++$cases;

            if (!($else instanceof LeanIte))
                break;
        }

        $cases = implode(
            "\\\\",
            array_fill(0, $cases, "%s")
        );
        return "\\begin{cases} $cases \\\\ {%s} & {\\color{blue}\\text{else}} \\end{cases}";
    }

    public function relocate_last_comment()
    {
        $else = $this->else;
        if ($else instanceof LeanStatements || $else instanceof LeanIte)
            $else->relocate_last_comment();
    }
    public function set_line($line)
    {
        $this->line = $line;
        [$if, $then, $else] = $this->args;
        $line = $if->set_line($line);
        ++$line;
        $line = $then->set_line($line);
        ++$line;
        if (!($else instanceof LeanIte))
            ++$line;
        return $else->set_line($line);
    }
    public function split(&$syntax = null)
    {
        [$if, $then, $else] = $this->args;
        if ($then && $else) {
            $self = clone $this;
            [$if, $then, $else] = $self->args;
            $self->args = [$if];
            $statements[] = $self;
            if ($then instanceof LeanStatements)
                $then->swap_echo_star($syntax, $statements);
            else
                $statements[] = $then;
            if ($else instanceof LeanIte) {
                $else = $else->split($syntax);
                $else[0]->args[2] = 0;
                array_push($statements, ...$else);
            } else {
                $statements[] = new LeanIte([], $this->indent, $else->level); // for else statement only;
                if ($else instanceof LeanStatements)
                    $else->swap_echo_star($syntax, $statements);
                else
                    $statements[] = $else;
            }
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        [$if, $then, $else] = $this->args;
        if (!$else && !$then) {
            // for split functions
            if ($if === null)
                return "else";
            if ($else === 0)
                return "else if %s then";
            return "if %s then";
        }
        $indent_else = str_repeat(' ', $this->indent);
        $sep = $else instanceof LeanIte ? ' ' : "\n";
        $then = $then == null? '' : '%s';
        $else = $else == null? '' : '%s';
        return "if %s then\n$then\n{$indent_else}else$sep$else";
    }

    static public function echo_part($part, $token) {
        $echo = new LeanTactic('echo', clone $token, $part->indent, $part->level);
        if ($part instanceof LeanStatements)
            $part->unshift($echo);
        else
            $part->parent->replace($part, new LeanStatements([$echo, $part], $part->indent, $part->level));
    }
}

// END OF ite family (LeanParser stays in lean.php)
