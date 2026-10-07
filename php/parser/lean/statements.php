<?php
/**
 * Statement lists (`LeanStatements`).
 *
 * Loaded by lean.php after `set.php` (`LeanArgs` and `LeanMultipleLine`
 * already exist). Mirrors static/js/parser/lean/statements.js. PHP `echo`,
 * `insert_newline`, and `latexFormat` stay shorter than JS. Later classes
 * (`LeanTactic`, `LeanBy`, `LeanModule`, …) are resolved when methods run.
 * Not a standalone entry point.
 */

class LeanStatements extends LeanArgs
{
    use LeanMultipleLine;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority;
            default:
                return parent::__get($vname);
        }
    }
    public function echo()
    {
        $args = &$this->args;
        $count = count($args);
        $void_lines = 0;
        // skip trailing carets and comments
        while (($last = $args[$count - 1]) instanceof LeanCaret || $last instanceof LeanLineComment || $last instanceof LeanBlockComment) {
            --$count;
            ++$void_lines;
        }
        for ($index = 0; $index < count($args) - $void_lines - 1; ++$index) {
            $result = $args[$index]->echo();
            if (is_array($result)) {
                // zero-th element is the length to be replaced
                $length = array_shift($result);
                if ($index + 1 < count($args) - $void_lines && $args[$index + 1] instanceof LeanTactic && $args[$index + 1]->func == 'try' && 
                    count($result) == 2 && $result[0] === $args[$index] && $result[1] instanceof LeanTactic && $result[1]->func == 'echo') {
                    // next tactic is 'try', so the current echo tactic should also be 'try echo ..'
                    $result[1] = new LeanTactic('try', $result[1], $result[1]->indent, $result[1]->level);
                }
                foreach ($result as $echo)
                    $echo->parent = $this;
                $increment = std\index($result, $args[$index]);
                array_splice($args, $index, $length, $result);
                $index += $increment;
            }
        }
        $tactic = $args[$index];
        if ($tactic instanceof LeanTactic || $tactic instanceof Lean_match) {
            if (($with = $tactic->with)) {
                if ($with->sep() == "\n") {
                    foreach ($with->args as $case)
                        $case->echo();
                } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator) {
                    if (($block = $sequential_tactic_combinator->arg) instanceof LeanTacticBlock)
                        $block->echo();
                    else
                        $sequential_tactic_combinator->echo();
                }
            } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator)
                $sequential_tactic_combinator->echo();
            else if ($block = $tactic->repeat_block())
                $block->echo();
        } elseif ($tactic instanceof LeanTacticBlock || $tactic instanceof LeanIte || $tactic instanceof LeanCalc)
            $tactic->echo();
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanIte([$caret], $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    /** Body of a multi-line structure-instance literal (see LeanBrace::openStructInstBody): one field per line. */
    public $structInst = null;

    /** The first field sits on the `{` / `with` line (no line prefix of its own). */
    public function isInlineFirst()
    {
        $p = $this->parent;
        return $this->structInst === true && ($p instanceof LeanBrace || $p instanceof LeanWith) && $p->inline === true;
    }

    public function push_binary($func)
    {
        // In a brace body (`{⏎ a := 1⏎ b := 2⏎ }`, or the `structInst` body of `{ a := 1⏎ b := 2 }` /
        // `{ s with⏎ … }`) `x := v` starts the next structure-instance field (mirrors statements.js).
        $parent = $this->parent;
        if ($parent && $func === 'LeanAssign' && ($this->structInst === true || $parent instanceof LeanBrace)) {
            $idx = count($this->args) - 1;
            while ($idx >= 0 && ($this->args[$idx] instanceof LeanCaret || $this->args[$idx] instanceof LeanLineComment || $this->args[$idx] instanceof LeanBlockComment))
                --$idx;
            if ($idx >= 0) {
                $this->structInst = true;
                $origin = $this->args[$idx];
                $caret = new LeanCaret($origin->indent, $origin->level);
                $this->replace($origin, new LeanAssign($origin, $caret, $origin->indent, $origin->level));
                return $caret;
            }
        }
        return parent::push_binary($func);
    }

    public function insert_comma($caret)
    {
        // `a := 1,⏎ b := 2`: a comma after a field of a structure-instance body
        if ($this->structInst === true && in_array($caret, $this->args, true)) {
            $c2 = new LeanCaret($caret->indent, $caret->level);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $c2], $caret->indent, $caret->level));
            return $c2;
        }
        return parent::insert_comma($caret);
    }

    public function strArgs()
    {
        $args = parent::strArgs();
        if (!$this->isInlineFirst() || !count($args))
            return $args;
        $args[0] = ltrim(strval($args[0]), ' ');
        return $args;
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            $wrapped = $this->push_args_indented($indent, $newline_count);
            if ($wrapped)
                return $wrapped;
            // Match JS LeanStatements.insert_newline: if the last arg cannot be
            // wrapped, fall through and append carets at the deeper indent.
        }

        for ($i = 0; $i < $newline_count; ++$i) {
            $caret = new LeanCaret($indent, $caret->level);
            $this->push($caret);
        }
        return $caret;
    }

    public function is_indented()
    {
        return false;
    }
    public function isProp($vars)
    {
        $args = &$this->args;
        if (count($args) == 1)
            return $args[0]->isProp($vars);
    }
    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof LeanCaret)
            array_pop($args);
        if (count($args) == 1)
            [$args] = $args;
        return $args;
    }

    public function latexFormat()
    {
        $stmt = implode(
            "\\\\\n",
            array_fill(0, count($this->args), "&{%s}&& ")
        );
        if ($this->parent instanceof LeanBy)
            return $stmt;
        return "\\begin{align*}\n$stmt\n\\end{align*}";
    }

    public function relocate_last_comment()
    {
        for ($index = count($this->args) - 1; $index >= 0; --$index) {
            $end = $this->args[$index];
            if ($end->is_outsider()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LeanStatements)
                        break;
                    $self = $parent;
                }
                if ($parent) {
                    $last = array_pop($this->args); // $end === $last
                    std\array_insert(
                        $parent->args,
                        std\index($parent->args, $self) + 1,
                        $last
                    );
                    $last->parent = $parent;
                    $last->indent = $parent->indent;
                    $parent->relocate_last_comment();
                    break;
                }
            } else {
                if ($end->is_comment()) {
                    $lemma = null;
                    for ($j = $index - 1; $j >= 0; --$j) {
                        $stmt = $this->args[$j];
                        if ($stmt instanceof Lean_lemma) {
                            $lemma = $stmt;
                            break;
                        }
                        if ($stmt->is_comment())
                            continue;
                        else
                            break;
                    }
                    if ($lemma) {
                        $assignment = $lemma->assignment;
                        if ($assignment instanceof LeanAssign) {
                            $proof = $assignment->rhs;
                            if ($proof instanceof LeanBy || $proof instanceof LeanCalc) {
                                $proof = $proof->arg;
                                if ($proof instanceof LeanStatements) {
                                    for ($i = $j + 1; $i <= $index; ++$i)
                                        $proof->push($this->args[$i]);
                                    array_splice($this->args, $j + 1, $index - $j);
                                    break;
                                }
                            } elseif ($proof instanceof LeanArgsNewLineSeparated) {
                                for ($i = $j + 1; $i <= $index; ++$i)
                                    $proof->push($this->args[$i]);
                                array_splice($this->args, $j + 1, $index - $j);
                                break;
                            }
                        }
                    }
                }
                $end->relocate_last_comment();
                break;
            }
        }
    }

    public function strFormat()
    {
        $format = implode("\n", array_fill(0, count($this->args), '%s'));
        if ($this->parent instanceof LeanBrace && !$this->parent->inline)
            $format = "\n$format\n" . str_repeat(' ', $this->parent->indent);
        return $format;
    }

    public function swap_echo_star(&$syntax, &$statements) {
        $args = &$this->args;
        for ($i = 0; $i < count($args); ++$i) {
            if (($echo = $args[$i]) instanceof LeanTactic && $echo->func == 'echo' && ($token = $echo->arg) instanceof LeanToken && $token->text == '*') {
                # convert `echo * simp at *` =>  `simp at * echo *`
                [$args[$i], $args[$i + 1]] = [$args[$i + 1], $args[$i]];
                ++$i;
            }
        }
        foreach ($this->args as $stmt)
            array_push($statements, ...$stmt->split($syntax));
    }

}

// END OF statements family (LeanParser stays in lean.php)
