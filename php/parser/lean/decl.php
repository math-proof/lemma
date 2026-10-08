<?php
/**
 * Declarations and binders (`Lean_def`, `theorem` / `abbrev` / `lemma`,
 * `let` / `have` / `set` / `replace` / `show`).
 *
 * Loaded by lean.php after `tactic.php` and before `Lean_fun`. Extends
 * `LeanArgs` / `LeanSyntax`, which already exist. Mirrors
 * static/js/parser/lean/decl.js. Not a standalone entry point.
 */

class Lean_def extends LeanArgs
{
    public function __construct($accessibility, $name, $indent = null, $level = null, $parent = null)
    {
        if ($level === null) {
            $indent = $name;
            $name = $accessibility;
            $accessibility = 'public';
        }
        parent::__construct([$name], $indent, $level, $parent);
        array_unshift($this->args, null);
        $this->accessibility = $accessibility;
    }
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            case 'operator':
                return 'def';
            case 'attribute':
                return $this->args[0] ?? null;
            case 'assignment':
                return $this->args[1] ?? null;
            case 'accessibility':
                return $this->kwargs['accessibility'];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'attribute':
                $this->args[0] = $val;
                break;
            case 'assignment':
                $this->args[1] = $val;
                break;
            case 'accessibility':
                $this->kwargs['accessibility'] = $val;
                return;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->assignment) {
                if ($new = $this->push_args_indented($indent, $newline_count))
                    return $new;
                if ($caret instanceof LeanColon) {
                    if ($caret->rhs instanceof LeanCaret) {
                        $caret = $caret->rhs;
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LeanStatements([$caret], $indent, $caret->level);
                        return $caret;
                    }
                } elseif ($caret instanceof LeanAssign) {
                    $rhs = $this->assignment->rhs;
                    if ($rhs instanceof LeanCaret) {
                        $rhs->indent = $indent;
                        $this->assignment->rhs = new LeanStatements([$rhs], $indent, $rhs->level);
                        return $rhs;
                    }
                    if ($rhs instanceof LeanArgsNewLineSeparated || $rhs instanceof LeanStatements) {
                        $c = new LeanCaret($indent, $rhs->level);
                        $rhs->push($c);
                        return $c;
                    }
                    return parent::insert_newline($caret, $newline_count, $indent, $next);
                }
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        $json = [
            $this->operator => parent::jsonSerialize(),
            "accessibility" => $this->accessibility
        ];
        if ($this->attribute)
            $json['attribute'] = $this->attribute->jsonSerialize();
        return $json;
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function relocate_last_comment()
    {
        $assignment = $this->assignment;
        if ($assignment instanceof LeanAssign)
            $assignment->relocate_last_comment();
    }

    public function set_line($line)
    {
        $this->line = $line;
        $attribute = $this->attribute;
        if ($attribute)
            $line = $attribute->set_line($line) + 1;
        return $this->assignment->set_line($line);
    }

    public function strArgs()
    {
        [$attribute, $assignment] = $this->args;
        if ($attribute == null)
            return [$assignment];
        return $this->args;
    }

    public function strFormat()
    {
        $accessibilityString = $this->accessibility == 'public' ? '' : "$this->accessibility ";
        $def = "$accessibilityString$this->func %s";
        if ($this->attribute)
            $def = "%s\n$def";
        return $def;
    }

}

class Lean_theorem extends Lean_def {}

class Lean_abbrev extends Lean_def {}

class Lean_lemma extends Lean_def
{
    public function echo()
    {
        $this->assignment->echo();
        if ($this->assignment instanceof LeanAssign && $this->assignment->rhs instanceof LeanBy) {
            $statement = $this->assignment->rhs->arg;
            if ($statement instanceof LeanStatements) {
                $statements = &$statement->args;
                for ($i = count($statements) - 1; $i >= 0; --$i) {
                    $stmt = $statements[$i];
                    if ($stmt->is_comment())
                        continue;
                    if ($stmt instanceof LeanTactic || $stmt instanceof Lean_let) {
                        $token = $stmt->get_echo_token();
                        // try echo ⊢
                        if ($token) {
                            $indent = $statement->indent;
                            $level = $statement->level;
                            $statement->push(new LeanTactic(
                                'try',
                                new LeanTactic('echo', $token, $indent, $level),
                                $indent,
                                $level
                            ));
                        }
                        break;
                    }
                }
            }
        }
    }
}

class Lean_let extends LeanSyntax
{
    /** parsed from `letI` / `haveI` (instance variant): same tree as `let` / `have`, only the keyword differs */
    public $inst = false;

    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct([$arg], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            case 'operator':
            case 'command':
                return 'let';
            case 'keyword':
                // source keyword: `operator`, or its instance variant `letI` / `haveI`
                return $this->inst ? $this->operator . 'I' : $this->operator;
            case 'sequential_tactic_combinator':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LeanSequentialTacticCombinator)
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
        $proof = $this->args[0]->rhs ?? null;
        if ($proof instanceof LeanBy) {
            $stmt = $proof->arg;
            if ($stmt instanceof LeanStatements)
                $stmt->echo();
        } elseif ($proof instanceof LeanCalc) {
            $proof->echo();
        }
        if ($token) {
            return [
                1,
                $this,
                new LeanTactic('echo', $token, $this->indent, $token->level)
            ];
        }
    }

    public function get_echo_token()
    {
        $assign = $this->args[0];
        if ($assign instanceof LeanAssign) {
            $angleBracket = $assign->lhs;
            if ($angleBracket instanceof LeanAngleBracket) {
                $token = $angleBracket->tokens_comma_separated();
                if (count($token) == 1)
                    return $token[0];
                return new LeanArgsCommaSeparated($token, $this->indent, $angleBracket->level);
            }
        }
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->args[0]) {
            if ($next == '<' && $this->parent instanceof LeanSequentialTacticCombinator) {
                // possibly newline-indented <;>
                $caret = new LeanCaret($indent, $caret->level);
                $this->push($caret);
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
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
    public function is_indented()
    {
        return !($this->parent instanceof LeanSequentialTacticCombinator);
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => $this->args[0]->jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        //cm-def {color: #00f;} 
        //defined in node_modules/codemirror/lib/codemirror.css
        $command = $this->command . ($this->inst ? 'I' : '');
        return "{\\color{#00f}$command}\\ " . implode('\ ', array_fill(0, count($this->args), "%s"));
    }
    public function split(&$syntax = null)
    {
        $assign = $this->args[0];
        if ($assign instanceof LeanAssign) {
            $proof = $assign->rhs;
            if (
                ($proof instanceof LeanBy && $proof->arg instanceof LeanStatements) ||
                $proof instanceof LeanCalc
            ) {
                $statements = $assign->split($syntax);
                $statements[0] = new static($statements[0], $this->indent, $assign->level);
                $statements[0]->inst = $this->inst;
                return $statements;
            }
        }
        return [$this];
    }

    /** `let := v` / `have : T := v`: no name before `:=` / `:` */
    public function anonymous()
    {
        $assign = $this->args[0];
        if (!($assign instanceof LeanAssign))
            return false;
        $lhs = $assign->lhs;
        return $lhs instanceof LeanCaret || $lhs instanceof LeanColon && $lhs->lhs instanceof LeanCaret;
    }

    public function strFormat()
    {
        $func = $this->keyword;
        $args = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanCaret);
            elseif ($arg === $this->args[0] && $this->inst && $this->anonymous())
                $args[] = ''; // `letI := inst`
            elseif ($arg instanceof LeanSequentialTacticCombinator && $arg->newline)
                $args[] = "\n";
            else
                $args[] = ' ';
            $args[] = '%s';
        }
        return $func . implode('', $args);
    }

}

class Lean_have extends Lean_let
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'have';
            default:
                return parent::__get($vname);
        }
    }

    public function get_echo_token()
    {
        $assign = $this->args[0];
        if ($assign instanceof LeanAssign) {
            $token = $assign->lhs;
            if ($token instanceof LeanColon)
                $token = $token->lhs;
            if ($token instanceof LeanCaret)
                $token = new LeanToken('this', $this->indent, $token->level);
            if ($token instanceof LeanArgsSpaceSeparated && $token->args[0] instanceof LeanToken)
                $token = $token->args[0];
            if (
                $token instanceof LeanAngleBracket &&
                $token->arg instanceof LeanArgsCommaSeparated &&
                std\array_all(fn($arg) => $arg instanceof LeanToken, $token->arg->args)
            )
                $token = $token->arg;

            if ($token instanceof LeanToken || $token instanceof LeanArgsCommaSeparated)
                return $token;
        }
    }

    public function sep()
    {
        $assign = $this->args[0];
        if ($assign instanceof LeanAssign) {
            $lhs = $assign->lhs;
            if ($lhs instanceof LeanCaret || $lhs instanceof LeanColon && $lhs->lhs instanceof LeanCaret)
                return '';
        }
        return ' ';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->keyword$sep%s";
    }

}

class Lean_set extends Lean_let
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'set';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_replace extends Lean_have
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'replace';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_show extends LeanSyntax
{
    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct([$arg], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            case 'operator':
                return 'show';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements || $parent instanceof LeanArgsNewLineSeparated;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => parent::jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        //cm-def {color: #00f;} 
        //defined in node_modules/codemirror/lib/codemirror.css
        $func = "{\\color{#00f}$this->func}";
        return "$func\\ " . implode('\ ', array_fill(0, count($this->args), "%s"));
    }

    public function strFormat()
    {
        return "$this->func " . implode(' ', array_fill(0, count($this->args), "%s"));
    }

}

// END OF decl family (LeanParser stays in lean.php)
