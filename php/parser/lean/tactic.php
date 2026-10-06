<?php
/**
 * Syntax and tactics (`LeanSyntax`, `LeanTactic`, and the wrappers through
 * `LeanAttribute`: `by`, `from`, `calc`, `at`, `<;>`, tactic blocks, `with`,
 * attributes).
 *
 * Loaded by lean.php after `args.php` and before `Lean_def`. Extends `LeanArgs`
 * / `LeanUnary`, which already exist. Mirrors static/js/parser/lean/tactic.js.
 * Not a standalone entry point.
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

class LeanBy extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'by';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_semicolon($caret)
    {
        if ($caret === $this->arg) {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanArgsSemicolonSeparated([$this->arg, $caret], $this->indent, $caret->level);
            return $caret;
        }
        return $this->parent->insert_semicolon($this);
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanArgsCommaNewLineSeparated;
    }
    public function latexFormat()
    {
        //cm-def {color: #00f;} 
        //defined in static/codemirror/lib/codemirror.css
        $arg = $this->arg;
        $command = "{\\color{#00f}$this->command}";
        if ($arg instanceof LeanStatements)
            return "\\begin{align*}\n$command && \\\\\n%s\n\\end{align*}";
        return "$command\\ %s";
    }
    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }
}

class LeanFrom extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'from';
            default:
                return parent::__get($vname);
        }
    }
    public function echo()
    {
        $this->arg->echo();
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanArgsCommaNewLineSeparated;
    }
    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }
    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }
}

class LeanCalc extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'calc';
            case 'stack_priority':
                return LeanAssign::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $echoStep = function ($stmt) {
            if ($stmt instanceof LeanAssign && ($by = $stmt->rhs) instanceof LeanBy && ($byArg = $by->arg) instanceof LeanStatements) {
                $indent = $byArg->indent;
                $level = $byArg->level;
                $byArg->unshift(new LeanTactic('echo', new LeanToken('⊢', $indent, $level), $indent, $level));
            }
            $stmt->echo();
        };
        $arg = $this->arg;
        if ($arg instanceof LeanArgsNewLineSeparated) {
            foreach ($arg->args as $stmt)
                $echoStep($stmt);
        } elseif ($arg instanceof LeanArgsIndented) {
            $echoStep($arg->rhs);
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret === $this->arg) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
                return $this->arg->push_newlines($newline_count - 1);
            }
            if ($caret instanceof LeanAssign) {
                $new = $this->push_args_indented($indent, $newline_count, false);
                if ($new)
                    return $new;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return !$parent || $parent instanceof LeanStatements || $parent instanceof LeanIte;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function sep()
    {
        return $this->arg instanceof LeanArgsNewLineSeparated ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanArgsNewLineSeparated)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function split(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanArgsNewLineSeparated) {
            $syntax['calc'] = true;
            $self = clone $this;
            $stmts = $self->arg->args;
            $self->arg = new LeanCaret($this->indent, $this->level);
            $statements = [$self];
            foreach ($stmts as $stmt) {
                array_push($statements, ...$stmt->split($syntax));
            }
            return $statements;
        }
        if ($arg instanceof LeanArgsIndented) {
            $syntax['calc'] = true;
            $self = clone $this;
            $arg = $self->arg;
            $content = $arg->rhs;
            $arg->rhs = new LeanCaret($content->indent, $content->level);
            $statements = [$self];
            array_push($statements, ...$content->split($syntax));
            return $statements;
        }
        return [$this];
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}


class LeanMOD extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'MOD';
            case 'command':
                return '\\operatorname{MOD}';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command\\$sep%s";
    }

    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}


class LeanUsing extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'using';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return $sep === "\n" ? "$this->command\n%s" : "$this->command %s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

class LeanAt extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'at';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return $sep === "\n" ? "{\\color{#00f}$this->command}\n%s" : "{\\color{#00f}$this->command}\ %s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

class LeanIn extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'in';
            case 'stack_priority':
                return 18;
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

class LeanGeneralizing extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'generalizing';
            default:
                return parent::__get($vname);
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent, $caret->level);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

class LeanSequentialTacticCombinator extends LeanUnary
{
    public $newline = null;
    public function __construct($arg, $indent, $level, $newline=false, $parent = null)
    {
        parent::__construct($arg, $indent, $level, $parent);
        $this->newline = $newline;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '<;>';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        if (($arg = $this->arg) instanceof LeanTacticBlock)
            $arg->echo();
        elseif ($arg->indent > 0) {
            $indent = $arg->indent;
            $level = $arg->level;
            $echo = new LeanTactic('echo', new LeanToken('⊢', $indent, $level), $indent, $level);
            if (($by_cases = $this->parent) instanceof LeanTactic && $by_cases->func == 'by_cases' && $by_cases->has_tactic_block_followed()) {
                while (($sequential_tactic_combinator = $arg->sequential_tactic_combinator) && $sequential_tactic_combinator->arg->indent)
                    $arg = $sequential_tactic_combinator;
                $arg->push(new LeanSequentialTacticCombinator($echo, $indent, $level, true));
            } else {
                $echo->push(new LeanSequentialTacticCombinator($arg, $indent, $level, $this->newline));
                $this->arg = $echo;
                $arg->echo();
            }
        }
    }

    public function getEcho()
    {
        if ($this->newline) {
            $echo = $this->arg;
            if ($echo instanceof LeanTactic && $echo->func == 'echo')
                return $echo;
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret instanceof LeanCaret && $caret === $this->arg) {
            if ($next == '·' || $next == '.') {
                if ($indent == $this->indent) {
                    $caret->indent = $indent;
                    return $caret;
                }
            } else {
                if ($indent > $this->indent)
                    $indent = $this->indent + 2;
                else
                    $indent = $this->indent;
                $caret->indent = $indent;
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret instanceof LeanCaret) {
            $this->arg = new LeanTactic($type, $caret, $caret->indent, $caret->level);
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return $this->newline;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanTacticBlock || $this->arg->indent > 0 && !$this->newline ? "\n" : ' ';
    }
    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanTacticBlock || $this->arg->indent >= $this->indent)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function split(&$syntax = null)
    {
        if (!$this->newline)
            return [$this];
        $arg = $this->arg;
        $args = $arg->split($syntax);
        $self = clone $this;
        $self->arg = $args[0];
        $args[0] = $self;
        return $args;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

class LeanTacticBlock extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '·';
            case 'command':
                return '\cdot';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $statements = $this->arg;
        if ($statements instanceof LeanStatements) {
            $statements->echo();
            if ($this->parent instanceof LeanSequentialTacticCombinator) {
                if (
                    $this->parent->parent instanceof LeanTactic &&
                    ($with = $this->parent->parent->with) &&
                    ($token = $with->unique_token($statements->indent))
                );
                else
                    $token = new LeanToken('⊢', $statements->indent, $statements->level);
                $statements->unshift(new LeanTactic('echo', $token, $statements->indent, $statements->level));
            } elseif ($this->parent instanceof LeanStatements) {
                $index = std\index($this->parent->args, $this);
                $tacticBlockCount = 0;
                foreach (std\range($index - 1, -1, -1) as $i) {
                    $stmt = $this->parent->args[$i];
                    if ($stmt->is_comment())
                        continue;

                    if ($stmt instanceof LeanTacticBlock) {
                        ++$tacticBlockCount;
                        continue;
                    }

                    if ($stmt instanceof LeanTactic) {
                        if ($stmt->func == 'echo')
                            continue;
                        switch ($stmt->func) {
                            case 'rcases':
                                if (($with = $stmt->with) instanceof LeanWith && ($tokens = $with->tokens_bar_separated()) && $tacticBlockCount < count($tokens)) {
                                    $token = $tokens[$tacticBlockCount];
                                    $indent = $statements->indent;
                                    $level = $statements->level;
                                    if (is_array($token)) {
                                        $token = array_filter($token, fn($token) => $token->text != 'rfl');
                                        $token = [...$token];
                                        $token = array_map(function ($token) use ($indent, $level) {
                                            $token = clone $token;
                                            $token->indent = $indent;
                                            $token->level = $level;
                                            return $token;
                                        }, $token, $level);
                                        if (count($token) == 1)
                                            [$token] = $token;
                                        else
                                            $token = new LeanArgsCommaSeparated($token, $indent, $level);
                                    } else {
                                        $token = clone $token;
                                        $token->indent = $indent;
                                        $token->level = $level;
                                    }
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $indent,
                                        $level,
                                    ));
                                }
                                break;
                            case "cases'":
                                if (($with = $stmt->with) instanceof LeanWith && ($tokens = $with->tokens_space_separated()) && $tacticBlockCount < count($tokens)) {
                                    $token = $tokens[$tacticBlockCount];
                                    $token = clone $token;
                                    $token->indent = $statements->indent;
                                    $token->level = $statements->level;
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $statements->indent,
                                        $statements->level,
                                    ));
                                }
                                break;
                            case 'obtain':
                                if (($assign = $stmt->arg) instanceof LeanAssign && (($bitOr = $assign->lhs) instanceof LeanBitOr) && ($tokens = $bitOr->tokens_bar_separated()) && $tacticBlockCount < count($tokens)) {
                                    $token = $tokens[$tacticBlockCount];
                                    $token = clone $token;
                                    $token->indent = $statements->indent;
                                    $token->level = $statements->level;
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $statements->indent,
                                        $statements->level,
                                    ));
                                }
                                break;
                            case 'split_ifs':
                                if (($with = $stmt->with) instanceof LeanWith && count($with->args) == 1 && (($tokens = $with->args[0]) instanceof LeanArgsSpaceSeparated || $tokens instanceof LeanToken)) {
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        new LeanToken(
                                            '⊢',
                                            $statements->indent,
                                            $statements->level
                                        ),
                                        $statements->indent,
                                        $statements->level
                                    ));
                                    if ($tokens = $tokens->tactic_block_info()[$tacticBlockCount]?? null) {
                                        $span = array_map(fn($token) => $token->cache['size'], $tokens);
                                        $args = array_slice($this->parent->args, $index);
                                        $length = count($args);
                                        foreach ($span as $i => $span_i) {
                                            $token = $tokens[$i];
                                            $token = clone $token;
                                            $token->indent = $this->indent;
                                            $stop = $this->tactic_block($args, $span_i);
                                            $new_list = array_slice($args, 0, $stop);
                                            $first = $new_list[0];
                                            if ($first instanceof LeanTactic && $first->func == 'echo') {
                                                if ($first->arg instanceof LeanToken)
                                                    $first->arg = new LeanArgsCommaSeparated([$token, $first->arg], $this->indent, $token->level);
                                                else
                                                    $first->arg->unshift($token);
                                            } else
                                                array_unshift($new_list, new LeanTactic(
                                                    'echo',
                                                    $token,
                                                    $this->indent,
                                                    $token->level
                                                ));
                                            $last = end($new_list);
                                            if ($last instanceof LeanTactic && $last->func == 'echo') {
                                                if ($last->arg instanceof LeanToken)
                                                    $last->arg = new LeanArgsCommaSeparated([$last->arg, $token], $this->indent, $token->level);
                                                else
                                                    $last->arg->push($token);
                                            } else
                                                array_push($new_list, new LeanTactic(
                                                    'echo',
                                                    $token,
                                                    $this->indent,
                                                    $token->level
                                                ));
                                            array_splice($args, 0, $stop, $new_list);
                                        }
                                        if ($index) {
                                            $prev = $this->parent->args[$index - 1];
                                            if ($prev instanceof LeanTactic && $prev->func == 'echo') {
                                                $first = array_shift($args);
                                                if ($prev->arg instanceof LeanToken) {
                                                    if ($first->arg instanceof LeanToken)
                                                        $prev->arg = new LeanArgsCommaSeparated([$prev->arg, $first->arg], $this->indent, $prev->arg->level);
                                                    else
                                                        $prev->arg = new LeanArgsCommaSeparated([$prev->arg, ...$first->arg->args], $this->indent, $prev->arg->level);
                                                } else {
                                                    if ($first->arg instanceof LeanToken)
                                                        $prev->arg->push($first->arg);
                                                    else {
                                                        foreach ($first->arg->args as $arg) {
                                                            $prev->arg->push($arg);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        return [$length, ...$args];
                                    }
                                }
                                break;

                            case 'by_cases':
                                if (($colon = $stmt->arg) instanceof LeanColon && ($token = $colon->lhs) instanceof LeanToken) {
                                    $tokens = $token->tokens_space_separated();
                                    $token = $tokens[$tacticBlockCount] ?? null;
                                    if ($token) {
                                        $token = clone $token;
                                        $token->indent = $this->indent;
                                        $token->level = $this->level;
                                        $echo = new LeanTactic(
                                            'echo',
                                            $token,
                                            $this->indent,
                                            $this->level,
                                        );
                                        return [1, $echo, $this, clone $echo];
                                    }
                                }
                                break;
                            case 'split':
                                if ($at = $stmt->at) {
                                    if (($at = $stmt->at) && ($token = $at->arg) instanceof LeanToken) {
                                        $token = clone $token;
                                        $token->indent = $statements->indent;
                                        $token->level = $statements->level;
                                        $statements->unshift(new LeanTactic(
                                            'echo',
                                            $token,
                                            $statements->indent,
                                            $statements->level,
                                        ));
                                    }
                                    break;
                                }
                            default:
                                $token = new LeanToken('⊢', $statements->indent, $statements->level);
                                $sequential_tactic_combinator = $stmt->sequential_tactic_combinator;
                                if ($sequential_tactic_combinator) {
                                    $tactic = $sequential_tactic_combinator->arg;
                                    $tactic_token = $tactic->get_echo_token();
                                    if ($tactic_token) {
                                        if ($tactic_token instanceof LeanArgsCommaSeparated) {
                                            $tactic_token->push($token);
                                            $token = $tactic_token;
                                        } else
                                            $token = new LeanArgsCommaSeparated([$tactic_token, $token], $statements->indent, $statements->level);
                                    }
                                }
                                $statements->unshift(new LeanTactic(
                                    'echo',
                                    $token,
                                    $statements->indent,
                                    $statements->level,
                                ));
                                break;
                        }
                    }
                    break;
                }
            }
        }
    }

    // return the stop (right open) index of the range [0, stop) that contains $span elements of LeanTacticBlock
    public function insert_line_comment($caret, $comment)
    {
        if ($caret instanceof LeanCaret) {
            $indent = $this->indent + 2;
            $new = new LeanLineComment($comment, $indent, $caret->level);
            $this->arg = new LeanStatements([$new], $indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LeanCaret) {
                if ($this->indent <= $indent) {
                    if ($indent == $this->indent)
                        $indent = $this->indent + 2;
                    $caret->indent = $indent;
                    $this->arg = new LeanStatements([$caret], $indent, $caret->level);
                    for ($i = 1; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($indent, $caret->level);
                        $this->arg->push($caret);
                    }
                    return $caret;
                }
            } elseif ($caret instanceof LeanStatements) {
                $block = $caret;
                if ($indent >= $block->indent) {
                    for ($i = 0; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($block->indent, $block->level);
                        $block->push($caret);
                    }
                    return $caret;
                }
            } elseif ($this->indent < $indent) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->arg->indent = $indent;
                $this->arg = new LeanStatements([$this->arg, $caret], $indent, $caret->level);
                return $caret;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        return true;
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ($this->arg instanceof LeanCaret ? '': ' ');
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function split(&$syntax = null)
    {
        if ($this->arg instanceof LeanStatements) {
            $self = clone $this;
            $stmts = $self->arg;
            $self->arg = new LeanCaret($this->indent, $self->arg->level);
            $statements = [$self];
            $stmts->swap_echo_star($syntax, $statements);
            return $statements;
        }
        return [$this];
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

    public function tactic_block($args, $span) {
        $count = 0;
        for ($j = 0; $count < $span && $j < count($args); ++$j) {
            if ($args[$j] instanceof LeanTacticBlock)
                ++$count;
        }
        return $j;
    }

}


class LeanWith extends LeanArgs
{
    /**
     * Walk ancestors for a LeanWith at $indent and return/create a caret for the next
     * alternative bar (|). Mirrors LeanWith.findAlternativeCaret in static/js/parser/lean.js.
     */
    public static function findAlternativeCaret($node, $indent)
    {
        for ($p = $node; $p; $p = $p->parent) {
            if ($p instanceof LeanWith && $p->indent === $indent) {
                $cases = $p->args;
                if (count($cases) > 0) {
                    $c = end($cases);
                    if ($c instanceof LeanCaret)
                        return $c;
                    if ($c instanceof LeanBar || $c->is_comment()) {
                        $nc = new LeanCaret($p->indent, $c->level);
                        $p->push($nc);
                        return $nc;
                    }
                }
            }
        }
        return null;
    }

    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct([$arg], $indent, $level, $parent);
    }
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof Lean_match)
                    return 23;
                return 17;
            case 'operator':
            case 'command':
                return 'with';
            default:
                return parent::__get($vname);
        }
    }

    public function insert_bar($caret, $prev_token, $next)
    {
        $cases = $this->args;
        if (end($cases) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanBar($caret, $this->indent, $caret->level));
                return $caret;
            } else {
                $new = new LeanCaret($this->indent, $caret->level);
                $this->replace($caret, new LeanBitOr($caret, $new, $this->indent, $caret->level));
                return $new;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        $cases = $this->args;
        if (count($cases) > 0) {
            $caret = end($cases);
            if ($caret instanceof LeanCaret)
                return $caret;

            if ($next == '|') {
                if ($caret instanceof LeanBar || $caret->is_comment()) {
                    $caret = new LeanCaret($this->indent, $caret->level);
                    $this->push($caret);
                    return $caret;
                }
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        return parent::insert_tactic($caret, $token);
    }

    public function is_indented()
    {
        return false;
    }
    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function relocate_last_comment()
    {
        end($this->args)->relocate_last_comment();
    }

    public function sep()
    {
        if (count($this->args) > 1)
            return "\n";
        if (!count($this->args))
            return "";
        [$caret] = $this->args;
        return $caret instanceof LeanCaret || $caret->tokens_space_separated() || $caret instanceof LeanBitOr ? ' ' : "\n";
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->sep() == "\n")
            ++$line;
        foreach ($this->args as $arg)
            $line = $arg->set_line($line) + 1;
        return $line - 1;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep" . implode("\n", array_fill(0, count($this->args), '%s'));
    }

    public function tokens_bar_separated()
    {
        if (count($this->args) == 1 && $this->args[0] instanceof LeanBitOr)
            return $this->args[0]->tokens_bar_separated();
        return [];
    }

    public function tokens_space_separated()
    {
        if (count($this->args) == 1 && $this->args[0] instanceof LeanArgsSpaceSeparated)
            return $this->args[0]->tokens_space_separated();
        return [];
    }
    public function unique_token($indent)
    {
        if (count($this->args) == 1) {
            $stmt = $this->args[0];
            if ($stmt instanceof LeanBitOr || $stmt instanceof LeanArgsSpaceSeparated)
                return $stmt->unique_token($indent);
        }
    }

}

class LeanAttribute extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '@';
            default:
                return parent::__get($vname);
        }
    }
    public function append($new, $type)
    {
        return $this->push_accessibility($new, "public");
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->parent instanceof LeanTactic)
            return parent::insert_newline($caret, $newline_count, $indent, $next);
        return $caret;
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function push_accessibility($new, $accessibility)
    {
        switch ($new) {
            case 'Lean_theorem':
            case 'Lean_lemma':
            case 'Lean_def':
            case 'Lean_abbrev':
                $level = $this->level;
                $caret = new LeanCaret($this->indent, $level);
                $new = new $new($accessibility, $caret, $this->indent, $level);
                $this->parent->replace($this, $new);
                $new->attribute = $this;
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function sep()
    {
        return '';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

}

// END OF tactic family (LeanParser stays in lean.php)
