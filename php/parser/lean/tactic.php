<?php
/**
 * Syntax and tactics (`LeanSyntax`, `LeanTactic`).
 *
 * Loaded by lean.php after `args.php`. Extends `LeanArgs`, which already
 * exists. Mirrors static/js/parser/lean/tactic.js. Not a standalone entry point.
 */

abstract class LeanSyntax extends LeanArgs
{
    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'arg':
                $this->args[0] = $val;
                break;
            case 'sequential_tactic_combinator':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanSequentialTacticCombinator) {
                        $args[$index] = $val;
                        break;
                    }
                }
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args)) {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->push(new $func($caret, $this->indent, $caret->level));
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanTactic extends LeanSyntax
{
    public $func;
    public $only;

    public function __construct($func, $arg, $indent, $level, $parent = null)
    {
        parent::__construct([$arg], $indent, $level, $parent);
        $this->func = $func;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof LeanBy)
                    return LeanColon::$input_priority;
                if ($this->func == 'obtain')
                    return LeanAssign::$input_priority - 1;
                return LeanAssign::$input_priority;
            case 'arg':
                return $this->args[0];
            case 'modifiers':
                return array_slice($this->args, 1);
            case 'at':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanAt)
                        return $args[$index];
                }
                return;
            case 'with':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanWith)
                        return $args[$index];
                }
                return;
            case 'sequential_tactic_combinator':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanSequentialTacticCombinator)
                        return $args[$index];
                }
                return;
            case 'by':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanBy)
                        return $args[$index];
                }
                return;
            case 'arrow':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanRightarrow)
                        return $args[$index];
                }
                return;
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $token = $this->get_echo_token();
        $has_sequential_tactic_combinator = ($sequential_tactic_combinator = $this->sequential_tactic_combinator) && $sequential_tactic_combinator->arg->indent;
        if ($token) {
            $echo = new LeanTactic('echo', $token, $this->indent, $this->level);
            if ($token instanceof LeanToken && $token->text == '*')
                // echo * simp at *
                return [1, $echo, $this];
            if (($by = $this->by) && $by->arg instanceof LeanStatements)
                $by->echo();
            if ($has_sequential_tactic_combinator && $sequential_tactic_combinator->newline) {
                $echo->push($sequential_tactic_combinator);
                $this->sequential_tactic_combinator = new LeanSequentialTacticCombinator($echo, $this->indent, $this->level, true);
                $sequential_tactic_combinator->echo();
                return; 
            }
            return [1, $this, $echo];
        }
        if ($has_sequential_tactic_combinator)
            $sequential_tactic_combinator->echo();
        elseif ($block = $this->repeat_block())
            $block->echo();
    }

    public function getEcho()
    {
        if ($this->func == 'echo')
            return $this;
        if ($this->func == 'try' && $this->arg->func == 'echo')
            return $this->arg;
    }

    public function get_echo_token()
    {
        if ($at = $this->at) {
            $token = $at->arg;
            if ($this->func == 'split') {
                if ($this->has_tactic_block_followed())
                    return;
            } else {
                if ($token instanceof LeanArgsSpaceSeparated)
                    $token = new LeanArgsCommaSeparated(
                        array_map(fn($arg) => clone $arg, $token->args),
                        $this->indent,
                        $token->level
                    );
            }
        } else {
            $token = [];
            $⊢ = "⊢";
            switch ($this->func) {
                case 'intro':
                case 'by_contra':
                    $arg = $this->arg;
                    if ($arg instanceof LeanToken)
                        $token[] = clone $arg;
                    elseif ($arg instanceof LeanArgsSpaceSeparated) {
                        foreach ($arg->tokens_space_separated() as $arg) {
                            if ($arg instanceof LeanToken)
                                $token[] = clone $arg;
                            elseif (is_array($arg)) {
                                foreach ($arg as $a)
                                    $token[] = clone $a;
                            }
                        }
                    } elseif ($arg instanceof LeanAngleBracket) {
                        $arg = $arg->arg;
                        if ($arg instanceof LeanToken)
                            $token[] = clone $arg;
                        elseif ($arg instanceof LeanArgsCommaSeparated)
                            $token = array_map(fn($arg) => clone $arg, $arg->args);
                    }
                    break;
                case 'denote':
                case "denote'":
                    if ($this->arg instanceof LeanColon) {
                        $var = $this->arg->lhs;
                        if ($var instanceof LeanToken)
                            $token[] = clone $var;
                    }
                    $⊢ = null;
                    break;
                case 'by_cases':
                    if ($this->arg instanceof LeanColon) {
                        $var = $this->arg->lhs;
                        if ($var instanceof LeanToken) {
                            if ($this->has_tactic_block_followed())
                                return;
                            $token[] = clone $var;
                        }
                    }
                    break;
                case 'split_ifs':
                    if (($with = $this->with) && $with->sep() == ' ') {
                        if ($this->has_tactic_block_followed())
                            return;
                        $var = $with->args[0];
                        $var = $var->tokens_space_separated();
                        if ($var)
                            $token[] = clone $var[0];
                    }
                    break;
                case "cases'":
                    if (($with = $this->with) && $with->sep() == ' ') {
                        if ($this->sequential_tactic_combinator) {
                            $var = $with->args[0];
                            $var = $var->unique_token($this->indent);
                            if ($var)
                                $token[] = $var;
                        }
                    }
                    break;
                case "injection":
                    if (($with = $this->with) && $with->sep() == ' ') {
                        $var = $with->args[0];
                        if ($var instanceof LeanArgsSpaceSeparated)
                            $token = $var->args;
                        else
                            $token[] = $var;
                        $⊢ = null;
                    }
                    break;
                case 'rcases':
                    if (($with = $this->with) && ($tokens = $with->tokens_bar_separated())) {
                        if ($this->has_tactic_block_followed())
                            return;
                        foreach ($tokens as $arg) {
                            if (is_array($arg))
                                array_push($token, ...array_filter($arg, fn($token) => $token->text != 'rfl'));
                            elseif ($arg->text != 'rfl')
                                $token[] = $arg;
                            break;
                        }
                    }
                    break;
                case 'obtain':
                    $assign = $this->arg;
                    if ($assign instanceof LeanAssign) {
                        $arg = $assign->lhs;
                        if ($arg instanceof LeanAngleBracket) {
                            foreach ($arg->tokens_comma_separated() as $t) {
                                if ($t->text != 'rfl')
                                    $token[] = $t;
                            }
                        } elseif ($arg instanceof LeanBitOr) {
                            if ($this->has_tactic_block_followed())
                                return;
                            foreach ($arg->tokens_bar_separated() as $arg) {
                                if (is_array($arg))
                                    array_push($token, ...array_filter($arg, fn($t) => $t->text != 'rfl'));
                                elseif ($arg->text != 'rfl')
                                    $token[] = $arg;
                                break;
                            }
                        }
                    }
                    break;
                case 'specialize':
                    $arg = $this->arg;
                    if ($arg instanceof LeanArgsSpaceSeparated && ($arg = $arg->args[0]) instanceof LeanToken)
                        $token[] = clone $arg;
                    $⊢ = null;
                    break;
                case 'contrapose':
                case 'contrapose!':
                    $arg = $this->arg;
                    if ($arg instanceof LeanToken)
                        $token[] = clone $arg;
                    break;
                case 'sorry':
                case 'echo':
                    return;
                case 'try':
                    if ($this->arg instanceof LeanTactic && $this->arg->func == 'echo')
                        return;
            }
            if ($this->has_tactic_block_followed() || $this->parent instanceof LeanSequentialTacticCombinator);
            elseif ($⊢)
                $token[] = new LeanToken($⊢, $this->indent, $this->level);
            switch (count($token)) {
                case 0:
                    break;
                case 1:
                    $token = $token[0];
                    break;
                default:
                    $token = new LeanArgsCommaSeparated(
                        $token,
                        $this->indent,
                        $this->level
                    );
            }
        }
        return $token;
    }
    public function has_tactic_block_followed()
    {
        // check the next statement:
        // if the next statement is a tactic block, skipping echoing ⊢ since it will be done in the next tactic block
        // if the next statement isn't a tactic block, echo ⊢ as usual
        if ($this->parent instanceof LeanStatements) {
            $stmts = $this->parent->args;
            for ($index = std\index($stmts, $this) + 1; $index < count($stmts); ++$index) {
                $stmt = $stmts[$index];
                if ($stmt instanceof LeanTacticBlock)
                    return true;
                if (!$stmt->is_comment())
                    break;
            }
        }
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LeanToken || $caret instanceof LeanArithmetic || $caret instanceof LeanPairedGroup) {
                $new = new LeanCaret($this->indent, $caret->level);
                $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level));
                return $new;
            }
            if ($caret instanceof LeanArgsCommaSeparated) {
                $new = new LeanCaret($this->indent, $caret->level);
                $caret->push($new);
                return $new;
            }
        }
        return parent::insert_comma($caret);
    }

    public function insert_line_comment($caret, $comment)
    {
        return $this->push_line_comment($comment);
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->arg) {
            if ($this->indent < $indent) {
                if ($caret instanceof LeanArgsSpaceSeparated) {
                    $new = new LeanCaret($this->indent, $caret->level);
                    $caret->push($new);
                    return $new;
                }
                // `change` / `refine` / … with the term on the next indented line:
                // keep it as this tactic's argument (not a sibling statement).
                if ($caret instanceof LeanCaret) {
                    $caret->indent = $indent;
                    $nl = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
                    $this->replace($caret, $nl);
                    return $nl->push_newlines($newline_count - 1);
                }
            }
            if ($next == '<') {
                // possibly newline-indented <;>
                $caret = new LeanCaret($indent, $caret->level);
                $this->push($caret);
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_only($caret)
    {
        if ($caret === end($this->args)) {
            $this->only = true;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_semicolon($caret)
    {
        if ($caret === $this->arg) {
            if ($this->is_inline_tactic_block()) {
                $new = new LeanCaret($this->indent, $caret->level);
                if ($caret instanceof LeanArgsSemicolonSeparated)
                    $caret->push($new);
                else
                    $this->replace($caret, new LeanArgsSemicolonSeparated([$caret, $new], $this->indent, $caret->level));
                return $new;
            }
            if ($this->parent instanceof LeanBy) {
                $new = new LeanCaret($this->indent, $caret->level);
                if ($caret instanceof LeanArgsSemicolonSeparated)
                    $caret->push($new);
                else
                    $this->parent->replace($this, new LeanArgsSemicolonSeparated([$this, $new], $this->indent, $caret->level));
                return $new;
            }
        }
        return parent::insert_semicolon($caret);
    }
    public function insert_sequential_tactic_combinator($caret, $next_token)
    {
        if ($caret === end($this->args)) {
            if ($caret instanceof LeanCaret)
                $this->replace($caret, new LeanSequentialTacticCombinator($caret, $this->indent, $caret->level, $next_token != "\n"));
            else {
                $caret = new LeanCaret(0, 0); # use 0 as the temporary indentation
                $this->push(new LeanSequentialTacticCombinator($caret, $this->indent, $caret->level));
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret === end($this->args) && $caret instanceof LeanCaret) {
            if ($this->is_inline_tactic_block()) {
                $this->replace($caret, new LeanTactic($type, $caret, $this->indent, $caret->level));
                return $caret;
            } else
                return $this->insert_word($caret, $type);
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return !$parent || ($parent instanceof LeanStatements || $parent instanceof LeanIte) || $parent instanceof LeanSequentialTacticCombinator && $this->indent >= $parent->indent && !$parent->newline;
    }

    public function is_inline_tactic_block()
    {
        return in_array($this->func, ['repeat', 'try']);
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
            'only' => $this->only,
            'modifiers' => array_map(fn($modifier) => $modifier->jsonSerialize(), $this->modifiers),
        ];
    }

    public function latexFormat()
    {
        $func = escape_specials($this->func);
        if ($this->only)
            $func .= '\ only';
        //cm-def {color: #00f;} 
        //cm-keyword {color: #708;} 
        //defined in static/codemirror/lib/codemirror.css
        $color = $func == 'sorry'? '708' : '00f';
        $func = "{\\color{#$color}$func}";
        if (!($this->arg instanceof LeanCaret))
            $func .= '\ ';
        return $func . implode('\ ', array_fill(0, count($this->args), "%s"));
    }

    public function push_line_comment($comment)
    {
        $new = new LeanLineComment($comment, $this->indent, $this->level);
        $this->push($new);
        return $new;
    }

    public function relocate_last_comment()
    {
        $arg = end($this->args);
        if ($arg instanceof LeanRightarrow || $arg instanceof LeanWith)
            $arg->relocate_last_comment();
    }

    public function repeat_block()
    {
        if ($this->func == 'repeat' && ($brace = $this->arg) instanceof LeanBrace && ($block = $brace->arg) instanceof LeanStatements)
            return $block;
    }

    public function split(&$syntax = null)
    {
        $syntax[$this->func] = true;
        if (($with = $this->with) && $with->sep() == "\n") {
            $self = clone $this;
            $self->with->args = [];
            $statements[] = $self;
            foreach ($with->args as $stmt)
                array_push($statements, ...$stmt->split($syntax));
            return $statements;
        }
        if ($sequential_tactic_combinator = $this->sequential_tactic_combinator) {
            $block = $sequential_tactic_combinator->arg;
            if ($block instanceof LeanTacticBlock) {
                if ($block->arg instanceof LeanStatements) {
                    $self = clone $this;
                    $block = $self->sequential_tactic_combinator->arg;
                    $stmts = $block->arg;
                    $block->arg = new LeanCaret(0, 0);
                    $statements = [$self];
                    $stmts->swap_echo_star($syntax, $statements);
                    return $statements;
                }
            } elseif (($block instanceof LeanTactic || $block instanceof Lean_have || $block instanceof Lean_let) && $block->indent >= $this->indent) {
                $self = clone $this;
                if ($sequential_tactic_combinator->newline) {
                    $block = $self->sequential_tactic_combinator;
                    assert(end($self->args) instanceof LeanSequentialTacticCombinator);
                    array_pop($self->args);
                } else {
                    $block = $self->sequential_tactic_combinator->arg;
                    $self->sequential_tactic_combinator->arg = new LeanCaret(0, 0);
                }
                $array = [$self];
                array_push($array, ...$block->split($syntax));
                return $array;
            }
            else {
                // unexpected case
            }
        }
        elseif ($block = $this->repeat_block()) {
            $self = clone $this;
            $self->arg = new LeanBrace(new LeanCaret($this->indent, $this->level), $this->indent, $this->level);
            $array = [$self];
            foreach ($block->args as $stmt)
                array_push($array, ...$stmt->split($syntax));
            $rbrace = new LeanBrace(new LeanCaret($this->indent, $this->level), $this->indent, $this->level);
            $rbrace->is_closed = false; // only the right brace is printed
            $array[] = $rbrace;
            return $array;
        }
        if (($by = $this->by) && ($stmts = $by->arg) instanceof LeanStatements) {
            $self = clone $this;
            $self->by->arg = new LeanCaret($by->indent, $by->level);
            $statements[] = $self;
            $stmts->swap_echo_star($syntax, $statements);
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        $func = $this->func;
        if ($this->only)
            $func .= " only";
        $args = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanCaret);
            elseif ($arg instanceof LeanSequentialTacticCombinator && $arg->newline)
                $args[] = "\n";
            elseif ($arg instanceof LeanArgsNewLineSeparated || $arg instanceof LeanArgsIndented)
                $args[] = "\n";
            else
                $args[] = ' ';
            $args[] = '%s';
        }
        return $func . implode('', $args);
    }

    public function set_line($line)
    {
        $this->line = $line;
        $L = $line;
        foreach ($this->args as $arg) {
            if ($arg == null)
                continue;
            if ($arg instanceof LeanCaret);
            elseif ($arg instanceof LeanSequentialTacticCombinator && $arg->newline)
                $L++;
            elseif ($arg instanceof LeanArgsNewLineSeparated || $arg instanceof LeanArgsIndented)
                $L++;
            $L = $arg->set_line($L);
        }
        return $L;
    }

}

// END OF tactic family (LeanBy stays in lean.php)
