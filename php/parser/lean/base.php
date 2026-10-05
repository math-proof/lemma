<?php
/**
 * Abstract Lean AST node (`Lean`).
 *
 * Loaded by lean.php before `LeanCaret`. Extends `IndentedNode`, which already
 * exists. Mirrors static/js/parser/lean/base.js. Not a standalone entry point.
 */

abstract class Lean extends IndentedNode
{
    public function __clone()
    {
        $this->parent = null;
    }

    public function __construct($indent, $level, $parent = null) {
        parent::__construct($indent, $parent);
        $this->level = $level; // nesting level for rainbow printing of parentheses
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                return $this->parent->root;
            case 'line':
                return $this->kwargs['line'];
            case 'stack_priority':
                return static::$input_priority;
            case 'level':
                return $this->kwargs['level'] ?? 0;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'line':
                $this->kwargs['line'] = $val;
                break;
            case 'level':
                $this->kwargs['level'] = $val;
                break;
            default:
                parent::__set($vname, $val);
        }
    }

    public function __toString()
    {
        return ($this->is_indented() ? str_repeat(' ', $this->indent) : '') . $this->toString();
    }

    public function append($new, $type)
    {
        if ($this->parent)
            return $this->parent->append($new, $type);
    }

    public function blockMatrixRows()
    {
        $rows = array_map(fn($n) => $n->hstackBlocks(), $this->flattenAppend());
        if (!$rows || in_array(null, $rows, true))
            return null;
        $cols = count($rows[0]);
        if ($cols < 1)
            return null;
        foreach ($rows as $r) {
            if (count($r) !== $cols)
                return null;
        }
        return $rows;
    }

    public function case_default($key, ...$kwargs)
    {
        return $this;
    }

    public function echo()
    {
    }

    public function flattenAppend()
    {
        $inner = $this->peelParen();
        if ($inner !== $this)
            return $inner->flattenAppend();
        return [$this];
    }

    public function getEcho() {}

    public function hstackBlocks()
    {
        $inner = $this->peelParen();
        if ($inner !== $this)
            return $inner->hstackBlocks();
        return null;
    }

    public function insert($caret, $func, $type)
    {
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }

    public function insert_assign($caret)
    {
        return $caret->push_binary('LeanAssign');
    }
    public function insert_bar($caret, $prev_token, $next)
    {
        switch ($next) {
            case ' ':
                if ($prev_token == ' ')
                    return $caret->push_arithmetic('|');
                return $this->push_right('LeanAbs');
            case ')':
                return $this->push_right('LeanAbs');
            default:
                if (!$next)
                    return $this->push_right('LeanAbs');
                return $this->insert_unary($caret, 'LeanAbs');
        }
    }

    public function insert_colon($caret)
    {
        return $caret->push_binary('LeanColon');
    }

    public function insert_comma($caret)
    {
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function insert_construct($caret)
    {
        return $caret->push_binary('LeanConstruct');
    }
    public function insert_else($caret)
    {
        if ($this->parent)
            return $this->parent->insert_else($this);
    }

    public function insert_end($caret)
    {
        if ($this->parent)
            return $this->parent->insert_end($this);
    }

    public function insert_left($caret, $func, $prev_token = '')
    {
        return $caret->push_left($func, $prev_token);
    }

    public function insert_line_comment($caret, $comment)
    {
        return $caret->push_line_comment($comment);
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function insert_semicolon($caret)
    {
        if ($this->parent)
            return $this->parent->insert_semicolon($this);
    }

    public function insert_sequential_tactic_combinator($caret, $next_token)
    {
        if ($this->parent)
            return $this->parent->insert_sequential_tactic_combinator($this, $next_token);
    }

    public function insert_space($caret)
    {
        return $caret;
    }

    public function insert_then($caret)
    {
        if ($this->parent)
            return $this->parent->insert_then($this);
    }
    public function insert_unary($self, $func)
    {
        $parent = $self->parent;
        if ($self instanceof LeanCaret) {
            $caret = $self;
            $new = new $func($caret, $self->indent, $self->level);
        } elseif ($self instanceof LeanArgsSpaceSeparated) {
            $caret = new LeanCaret($self->indent, $self->level);
            $new = new $func($caret, $self->indent, $self->level);
            $self->push($new);
            return $caret;
        } else {
            $caret = new LeanCaret($self->indent, $self->level);
            $new = new $func($caret, $self->indent, $self->level);
            $new = new LeanArgsSpaceSeparated([$self, $new], $self->indent, $self->level);
        }
        $parent->replace($self, $new);
        return $caret;
    }

    public function insert_vconstruct($caret)
    {
        return $caret->push_binary('LeanVConstruct');
    }
    public function insert_word($caret, $word)
    {
        return $caret->push_token($word);
    }

    public function is_comment()
    {
        return false;
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            $parent instanceof LeanStatements || 
            $parent instanceof LeanIte && ($this === $parent->then || $this === $parent->else);
    }

    public function isMatMulContext()
    {
        return false;
    }

    public function isMatMulOperand()
    {
        return $this->parent && $this->parent->isMatMulContext();
    }

    public function is_outsider()
    {
        return false;
    }

    public function isProp($vars)
    {
        return false;
    }

    public function is_space_separated()
    {
        return false;
    }

    public function latexArgs(&$syntax = null)
    {
        return array_map(
            function ($arg) use (&$syntax) {
                return $arg->toLatex($syntax);
            },
            $this->args
        );
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function matrixLatexArgs(&$syntax = null)
    {
        $rows = $this->matrixLatexSpec();
        if (!$rows)
            return null;
        $out = [];
        foreach ($rows as $row) {
            foreach ($row as $cell)
                $out[] = $cell->peelParen()->toLatex($syntax);
        }
        return $out;
    }

    public function matrixLatexSpec()
    {
        $rows = $this->blockMatrixRows();
        if ($rows)
            return $rows;
        if ($this->isMatMulOperand()) {
            $parts = $this->flattenAppend();
            if (count($parts) >= 2)
                return array_map(fn($p) => [$p], $parts);
        }
        return null;
    }

    function parse($token, ...$kwargs)
    {
        [$self] = $kwargs;
        $i = &$self->start_idx;
        $tokens = &$self->tokens;
        $count = count($tokens);
        switch ($token) {
            case 'import':
            case 'open':
            case 'namespace':
            case 'def':
            case 'abbrev':
            case 'theorem':
            case 'lemma':
            case 'set_option':
                return $this->append("Lean_$token", "delspec");
            case 'fun':
            case 'match':
                return $this->append("Lean_$token", "expr");
            case 'set':
                // `lemma set` — keyword is the declaration name, not a tactic.
                if ($this instanceof LeanCaret && $this->parent instanceof Lean_def)
                    return $this->parent->insert_word($this, $token);
            case 'have':
            case 'replace':
            case 'let':
            case 'show':
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty) {
                    while (preg_match("/['!?\w]/", $tokens[$i + 1])) {
                        ++$i;
                        $token .= $tokens[$i];
                    }
                    return $this->parent->insert_word($this, $token);
                }
                return $this->append("Lean_$token", "tactic");
            case 'lim':
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty)
                    return $this->parent->insert_word($this, $token);
                return $this->append('Lean_lim', 'operator');
            case 'public':
            case 'private':
            case 'protected':
                while ($tokens[++$i] == ' ');
                if ($tokens[$i] == 'nonrec') {
                    $token .= ' nonrec';
                    ++$i;
                    while ($tokens[++$i] == ' ');
                }
                return $this->push_accessibility("Lean_$tokens[$i]", $token);
            case 'scoped':
            case 'noncomputable':
            case 'nonrec':
                while ($tokens[++$i] == ' ');
                return $this->push_accessibility("Lean_$tokens[$i]", $token);
            case ' ':
                return $this->parent->insert_space($this);
            case "\t":
                throw new Exception("Tab is not allowed in Lean");
            case "\r":
                error_log("Carriage return is not allowed in Lean");
                break;
            case "\n":
                // return new NewLineSkippingCommentParser($this, true);
                $j = 0;
                $newline_count = 1;
                while (true) {
                    $indent = 0;
                    while ($tokens[$i + ++$j] == ' ')
                        ++$indent;
                    if ($tokens[$i + $j] != "\n")
                        break;
                    ++$newline_count;
                }
                $k = $j;
                while ($i + $k + 1 < $count && $tokens[$i + $k] == '-' && $tokens[$i + $k + 1] == '-') {
                    // skip line comment;
                    while ($tokens[$i + ++$k] != "\n");

                    while ($tokens[$i + $k] == "\n") {
                        $indent = 0;
                        while ($tokens[$i + ++$k] == ' ')
                            ++$indent;
                    }
                }
                if ($indent == 0 && $tokens[$i + $k] == 'end')
                    // end of namespace
                    $newline_count -= 1;
                $caret = null;
                $nextTok = $tokens[$i + $k] ?? null;
                // Match JS: when the next token is a with-alternative bar (|), attach the
                // caret under the LeanWith at this indent instead of bubbling insert_newline
                // (which can hit LeanStatements and throw).
                if (
                    $nextTok === '|' &&
                    ($tokens[$i + $k + 1] ?? null) !== '|' &&
                    ($tokens[$i + $k + 1] ?? null) !== '>'
                ) {
                    $caret = LeanWith::findAlternativeCaret($this->parent, $indent);
                }
                if (!$caret)
                    $caret = $this->parent->insert_newline($this, $newline_count, $indent, $nextTok);
                $i += $j - 1;
                return $caret;
            case '.':
                if ($tokens[$self->start_idx + 1] === '.') {
                    $self->start_idx++;
                    return $this->push_binary('LeanUpto');
                }
                if ($this instanceof LeanCaret && ($this->parent instanceof LeanStatements || $this->parent instanceof LeanSequentialTacticCombinator))
                    return $this->parent->insert_unary($this, 'LeanTacticBlock');
                else
                    return $this->push_binary("LeanProperty");
            case 'is':
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty)
                    return $this->parent->insert_word($this, $token);
                else {
                    $func = "Lean_$token";
                    $not = $i + 2 < $count && std\isspace($tokens[$i + 1]) && strtolower($tokens[$i + 2]) == 'not';
                    if ($not) {
                        $i += 2;
                        $func .= '_not';
                    }
                    return $this->push_binary($func);
                }
            case '(':
                return $this->parent->insert_left($this, 'LeanParenthesis');
            case ')':
                return $this->parent->push_right('LeanParenthesis');
            case '[':
                return $this->parent->insert_left($this, 'LeanBracket', $i ? $tokens[$i - 1] : '');
            case ']':
                return $this->parent->push_right('LeanBracket');
            case '{':
                return $this->parent->insert_left($this, 'LeanBrace');
            case '}':
                return $this->parent->push_right('LeanBrace');
            case '⟨':
                return $this->parent->insert_left($this, 'LeanAngleBracket');
            case '⟩':
                return $this->parent->push_right('LeanAngleBracket');
            case '⌈':
                return $this->parent->insert_left($this, 'LeanCeil');
            case '⌉':
                return $this->parent->push_right('LeanCeil');
            case '⌊':
                return $this->parent->insert_left($this, 'LeanFloor');
            case '⌋':
                return $this->parent->push_right('LeanFloor');
            case '«':
                return $this->parent->insert_left($this, 'LeanDoubleAngleQuotation');
            case '»':
                return $this->parent->push_right('LeanDoubleAngleQuotation');
            case '‹':
                return $this->parent->insert_left($this, 'LeanSingleAngleQuotation');
            case '›':
                return $this->parent->push_right('LeanSingleAngleQuotation');
            case '?':
                if ($this instanceof LeanGetElem) {
                    $parent = $this->parent;
                    [$lhs, $rhs] = $this->args;
                    $new = new LeanGetElemQue($lhs, $rhs, $this->indent, $this->level);
                    $parent->replace($this, $new);
                    return $new;
                } else {
                    if ($tokens[$i + 1] == '_') {
                        ++$i;
                        $token .= '_';
                    }
                    return $this->parent->insert_word($this, $token);
                }
            case '<':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('Lean_le');
                }
                if ($tokens[$i + 1] == '|') {
                    ++$i;
                    return $this->push_arithmetic('<|');
                }
                if ($i + 2 < $count && $tokens[$i + 1] == ';' && $tokens[$i + 2] == '>') {
                    $i += 2;
                    return $this->parent->insert_sequential_tactic_combinator($this, $tokens[$i + 1]);
                }
                if ($tokens[$i + 1] == '<') {
                    ++$i;
                    $token .= '<';
                    if ($tokens[$i + 1] == '<') {
                        ++$i;
                        $token .= '<';
                    }
                }
                return $this->push_arithmetic($token);
            case '>':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    $token .= '=';
                } elseif ($tokens[$i + 1] == '>') {
                    ++$i;
                    $token .= '>';
                    if ($tokens[$i + 1] == '>') {
                        ++$i;
                        $token .= '>';
                    }
                }
                return $this->push_arithmetic($token);
            case '≤':
                return $this->push_binary('Lean_le');
            case '≥':
                return $this->push_binary('Lean_ge');
            case '⟂':
                if ($tokens[$i + 1] == "\u{1D62}") {
                    // `⟂ᵢ[𝕡]` — independence with a measure modifier; the modifier is
                    // required by Lean's notation but elided in LaTeX (like `=ᵐ[ν]`)
                    ++$i; // consume `ᵢ`
                    $modifier = '';
                    if ($tokens[$i + 1] == '[') {
                        $i += 2; // skip `[`, point at first char inside
                        $start = $i;
                        while ($i < $count && $tokens[$i] != ']') ++$i;
                        $modifier = implode('', array_slice($tokens, $start, $i - $start));
                        if ($i < $count) ++$i; // skip `]`
                        --$i; // loop will increment
                    }
                    $caret = $this->push_binary('LeanIndep');
                    $p = $caret;
                    while ($p && !($p instanceof LeanIndep)) $p = $p->parent;
                    if ($p) $p->modifier = $modifier;
                    return $caret;
                }
                return $this->parent->insert_word($this, $token);
            case '=':
                if ($tokens[$i + 1] == '>') {
                    ++$i;
                    if ($this->parent instanceof LeanAt && $this->parent->parent instanceof LeanTactic) {
                        // conv_lhs at h => ...
                        $new = new LeanCaret($this->indent, $this->level);
                        $this->parent->parent->push($new);
                        return $new->push_binary('LeanRightarrow');
                    }
                    return $this->push_binary('LeanRightarrow');
                } elseif ($tokens[$i + 1] == "\u{1D50}" && $tokens[$i + 2] == '[') {
                    $i += 2;
                    $start = $i + 1;
                    while ($i < count($tokens) && $tokens[$i + 1] != ']') ++$i;
                    $modifier = implode('', array_slice($tokens, $start, $i - $start + 1));
                    $i++;
                    $node = $this->push_binary('LeanMEq');
                    $node->modifier = $modifier;
                    return $node;
                } elseif ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('LeanBEq');
                } else
                    return $this->push_binary('LeanEq');
            case '!':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('Lean_ne');
                } elseif ($this instanceof LeanCaret)
                    return $this->parent->insert_unary($this, 'LeanNot');
                else
                    return $this->push_post_unary('LeanFactorial');
            case ',':
                return $this->parent->insert_comma($this);
            case ':':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->parent->insert_assign($this);
                }
                if ($tokens[$i + 1] == ':') {
                    ++$i;
                    if ($tokens[$i + 1] == 'ᵥ') {
                        ++$i;
                        return $this->parent->insert_vconstruct($this);
                    } else
                        return $this->parent->insert_construct($this);
                }
                return $this->parent->insert_colon($this);
            case ';':
                return $this->parent->insert_semicolon($this);
            case '-':
                if ($tokens[$i + 1] == '-') {
                    ++$i;
                    $comment = "";
                    while ($tokens[++$i] != "\n")
                        $comment .= $tokens[$i];
                    --$i; // now $tokens[$i + 1] must be a new line;
                    return $this->parent->insert_line_comment($this, trim($comment));
                } elseif ($this instanceof LeanCaret)
                    return $this->parent->insert_unary($this, 'LeanNeg');
                else
                    return $this->push_arithmetic($token);
            case '*':
                if ($this instanceof LeanCaret)
                    return $this->parent->insert_word($this, $token);
                if ($this instanceof LeanToken && $this->is_TypeStar() && (!$i || $tokens[$i - 1] != ' ')) {
                    $this->text .= '*';
                    return $this;
                }
                return $this->push_arithmetic($token);
            case '|':
                $next = $tokens[$i + 1];
                if ($next == '|') {
                    ++$i;
                    if ($tokens[$i + 1] == '|') {
                        ++$i;
                        return $this->push_binary('LeanBitwiseOr');
                    } 
                    return $this->push_binary('LeanLogicOr');
                }
                if ($next == '>') {
                    ++$i;
                    if ($tokens[$i + 1] == '.') {
                        ++$i;
                        return $this->push_arithmetic('|>.');
                    }
                    return $this->push_post_unary('LeanPipeForward');
                }
                return $this->parent->insert_bar($this, $i? $tokens[$i - 1]: '', $next);
            case '&':
                if ($tokens[$i + 1] == '&') {
                    ++$i;
                    $token .= '&';
                    if ($tokens[$i + 1] == '&') {
                        ++$i;
                        $token .= '&';
                    }
                }
                return $this->push_arithmetic($token);
            case "'":
                if ($this instanceof LeanGetElem && $tokens[$i - 1] == ']') {
                    [$lhs, $rhs] = $this->args;
                    $caret = new LeanCaret($this->indent, $this->level);
                    $this->parent->replace($this, new LeanGetElemQuote([$lhs, $rhs, $caret], $this->indent, $this->level));
                    return $caret;
                }
                $prev_token = $tokens[$i - 1] ?? null;
                while (preg_match("/[\w'!?₀-₉]/u", $tokens[$i + 1]))
                    $token .= $tokens[++$i];
                if ($prev_token !== null && preg_match("/[\w'!?₀-₉]/u", (string)$prev_token))
                    return $this->push_quote($token);
                return $this->push_token($token);
            case '+':
                if ($this instanceof LeanCaret)
                    return $this->parent->insert_unary($this, 'LeanPlus');
                if ($tokens[$i + 1] == '+') {
                    ++$i;
                    $token .= '+';
                }
                return $this->push_arithmetic($token);
            case '^':
                if ($tokens[$i + 1] == '^') {
                    ++$i;
                    $token .= '^';
                    if ($tokens[$i + 1] == '^') {
                        ++$i;
                        $token .= '^';
                    } 
                }
                return $this->push_arithmetic($token);
            case '/':
                if ($tokens[$i + 1] == '-') {
                    ++$i;
                    if ($tokens[$i + 1] == '-') {
                        $docstring = true;
                        ++$i;
                    } else
                        $docstring = false;
                    $comment = "";
                    while (true) {
                        ++$i;
                        if ($tokens[$i] == '-' && $tokens[$i + 1] == '/') {
                            ++$i;
                            break;
                        }
                        $comment .= $tokens[$i];
                    }
                    $comment = preg_replace('/(?<=\n) +$/', '', $comment);
                    $comment = trim($comment, "\n");
                    if ($tokens[$i + 1] == "\n")
                        ++$i;
                    return $this->push_block_comment($comment, $docstring);
                }
                if ($tokens[$i + 1] == '/') {
                    ++$i;
                    return $this->push_arithmetic('//');
                }
            case '%':
            case '×':
            case '⬝':
            case '∘':
            case '•':
            case '⊙':
            case '⊗':
            case '⊕':
            case '⊖':
            case '⊘':
            case '⊚':
            case '⊛':
            case '⊜':
            case '⊝':
            case '⊞':
            case '⊟':
            case '⊠':
            case '⊡':
            case '∈':
            case '∉':
            case '▸':
            case '∪':
            case '∩':
            case '⊔':
            case '⊓':
            case "\\":
            case '⊆':
            case '⊇':
            case '⊂':
            case '⊃':
            case '→':
            case '↦':
            case '↔':
            case '∧':
            case '∨':
            case '≠':
            case '≡':
            case '≢':
            case '≃':
            case '≍':
            case '≈':
            case '∣':
                return $this->push_arithmetic($token);
            case '←':
                return $this->parent->insert_unary($this, 'Lean_leftarrow');
            case '∀':
                return $this->append('Lean_forall', 'operator');
            case '∃':
                return $this->append('Lean_exists', 'operator');
            case '∑':
                $caret = $this->append('Lean_sum', 'operator');
                // `∑'` (`tsum`): an apostrophe fused directly to `∑` (no whitespace) is
                // part of the operator — otherwise it would open a character literal.
                if ($tokens[$i + 1] === "'") {
                    $i++;
                    $p = $this;
                    while ($p && !($p instanceof Lean_sum)) $p = $p->parent;
                    if ($p) $p->prime = true;
                }
                return $caret;
            case '∏':
                return $this->append('Lean_prod', 'operator');
            case '⋃':
                return $this->append('Lean_bigcup', 'operator');
            case '⋂':
                return $this->append('Lean_bigcap', 'operator');
            case '∫':
                return $this->append('Lean_int', 'operator');
            case '∂':
                return $this->parent->insert_unary($this, 'Lean_partial');
            case '¬':
                return $this->parent->insert_unary($this, 'Lean_lnot');
            case '~':
                return $this->parent->insert_unary($this, 'LeanConj');
            case '√':
                return $this->parent->insert_unary($this, 'Lean_sqrt');
            case '∛':
                return $this->parent->insert_unary($this, 'LeanCubicRoot');
            case '∜':
                return $this->parent->insert_unary($this, 'LeanQuarticRoot');
            case '↑':
                return $this->parent->insert_unary($this, 'Lean_uparrow');
            case '¹':
                if ($this instanceof LeanToken) {
                    $this->text .= $token;
                    return $this;
                }
                return $this->parent->insert_word($this, $token);
            case '²':
                return $this->push_post_unary('LeanSquare');
            case '³':
                return $this->push_post_unary('LeanCube');
            case '⁴':
                return $this->push_post_unary('LeanTesseract');
            case 'ᵀ':
                return $this->push_post_unary('LeanTranspose');
            case '⁺':
                return $this->push_post_unary('LeanPosPart');
            case '⁻':
                if ($tokens[$i + 1] == '¹') {
                    ++$i;
                    return $this->push_post_unary('LeanInv');
                }
                return $this->push_post_unary('LeanNegPart');
            case 'by':
            # modifiers
            case 'using':
            case 'at':
            case 'with':
            case 'in':
            case 'generalizing':
            case 'MOD':
            case 'from':
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty) {
                    while (preg_match("/['!?\w]/", $tokens[$i + 1])) {
                        ++$i;
                        $token .= $tokens[$i];
                    }
                    return $this->parent->insert_word($this, $token);
                }
                $token = ucfirst($token);
                return $this->parent->insert($this, "Lean$token", "modifier");
            case 'calc': 
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty) {
                    while (preg_match("/['!?\w]/", $tokens[$i + 1])) {
                        ++$i;
                        $token .= $tokens[$i];
                    }
                    return $this->parent->insert_word($this, $token);
                }
                return $this->parent->insert_calc($this);
            case '·':
                if ($this->parent instanceof LeanStatements || $this->parent instanceof LeanSequentialTacticCombinator)
                    return $this->parent->insert_unary($this, 'LeanTacticBlock');
                else
                    //Middle Dot token
                    return $this->parent->insert_word($this, $token);
            case '@':
                if ($this instanceof LeanCaret) {
                    // `@[` is an attribute; `@expr` is explicit argument application
                    $next = $i + 1;
                    while ($tokens[$next] == ' ') $next++;
                    if ($tokens[$next] == '[')
                        return $this->parent->insert_unary($this, 'LeanAttribute');
                    return $this->parent->insert_word($this, '@');
                }
                return $this->push_binary('LeanMatMul');
            case 'end':
                return $this->parent->insert_end($this);
            case 'only':
                return $this->parent->insert_only($this);
            case 'if':
                return $this->parent->insert_if($this);
            case 'then':
                return $this->parent->insert_then($this);
            case 'else':
                return $this->parent->insert_else($this);
            case '‖':
                if ($this instanceof LeanCaret || $i && $tokens[$i - 1] == ' ')
                    return $this->parent->insert_left($this, 'LeanNorm');
                return $this->parent->push_right('LeanNorm');
            default:
                $token_orig = $token;
                global $tactics;
                $index = std\binary_search($tactics, $token_orig, "strcmp");
                while (preg_match("/[\w'!?₀-₉]/u", $tokens[$i + 1])) {
                    ++$i;
                    $token .= $tokens[$i];
                }
                if ($index < count($tactics) && $tactics[$index] == $token_orig)
                    return $this->parent->insert_tactic($this, $token);
                else
                    return $this->parent->insert_word($this, $token);
        }
    }

    public function peelLatexCoe()
    {
        return $this;
    }

    public function peelParen()
    {
        return $this;
    }

    /**
     * Peel pure grouping wrappers: parentheses and singleton space-separated
     * groups. Default leaves the node as-is; LeanParenthesis and singleton
     * LeanArgsSpaceSeparated override to recurse into their single child.
     */
    public function peelGroup()
    {
        return $this;
    }

    /**
     * Head text of an application chain `Measure Ω` / `M.Measure Ω` -> its head
     * identifier (e.g. `Measure`, `M.Measure`); null if none can be extracted.
     */
    public function appHead()
    {
        $g = $this->peelGroup();
        if ($g instanceof LeanToken) return $g->text;
        if ($g instanceof LeanArgsSpaceSeparated && count($g->args) >= 1) {
            $h = $g->args[0];
            if ($h instanceof LeanToken || $h instanceof LeanProperty) return trim((string)$h);
        }
        return null;
    }

    /** True if this node's appHead() equals $name or ends with ".$name". */
    public function headIs(string $name): bool
    {
        $h = $this->appHead();
        return $h === $name || ($h !== null && str_ends_with($h, '.' . $name));
    }

    /**
     * Binder names introduced by the lhs of `↦` / `x : T` / `x in s`.
     * @param object $node
     * @return string[]
     */
    protected static function binderNames($node): array
    {
        $names = [];
        $go = function ($x) use (&$go, &$names) {
            $y = $x->peelGroup();
            if ($y instanceof LeanToken) $names[] = $y->text;
            elseif ($y instanceof LeanColon) $go($y->lhs);
            elseif ($y instanceof LeanArgsSpaceSeparated)
                foreach ($y->args as $z) $go($z);
            // LeanIn (`in s`) carries the domain, not a name: do not descend
        };
        $go($node);
        return $names;
    }

    /**
     * Mark FREE occurrences of random-variable names on $this subtree by
     * calling setRandomVariable() on their tokens. Local binders
     * (`fun … ↦`, `∀`, big operators, and preceding `let` statements) shadow
     * same-named variables in their scope, so bound occurrences stay uncolored.
     * @param string[] $rvNames
     * @param string[] $letBound names introduced by preceding `let` statements
     */
    public function markRandomVarNames(array $rvNames, array &$letBound = []): void
    {
        /** @var array<string,bool> */
        $rvSet = array_flip($rvNames);
        /** @var string[][] */
        $localFrames = [];

        $isHidden = function ($name) use (&$letBound, &$localFrames) {
            if (in_array($name, $letBound, true)) return true;
            foreach ($localFrames as $f) if (in_array($name, $f, true)) return true;
            return false;
        };

        $walk = function ($n) use (&$walk, &$letBound, &$localFrames, $isHidden, $rvSet) {
            if (!$n || !is_object($n)) return;
            if ($n instanceof LeanToken) {
                if (isset($rvSet[$n->text]) && !$isHidden($n->text))
                    $n->setRandomVariable();
                return;
            }
            if ($n instanceof Lean_mapsto) {
                $localFrames[] = Lean::binderNames($n->lhs);
                $walk($n->rhs);
                array_pop($localFrames);
                return;
            }
            if ($n instanceof LeanBigOperator) {
                $localFrames[] = $n->bound ? Lean::binderNames($n->bound) : [];
                // domain/type of the bound variable is outside its own scope
                if ($n->bound instanceof LeanColon) $walk($n->bound->rhs);
                if ($n->scope) $walk($n->scope);
                array_pop($localFrames);
                return;
            }
            if ($n instanceof Lean_let) {
                // RHS is evaluated first; the name binds only the continuation
                $a = $n->args[0] ?? null;
                if ($a instanceof LeanAssign) {
                    if ($a->lhs instanceof LeanColon) {
                        $walk($a->lhs->rhs);
                        $walk($a->rhs);
                        foreach (Lean::binderNames($a->lhs->lhs) as $nm) $letBound[] = $nm;
                    } else {
                        $walk($a->rhs);
                        foreach (Lean::binderNames($a->lhs) as $nm) $letBound[] = $nm;
                    }
                } elseif ($a instanceof LeanColon && $a->rhs instanceof LeanAssign) {
                    $walk($a->rhs->rhs);
                    foreach (Lean::binderNames($a->rhs->lhs) as $nm) $letBound[] = $nm;
                }
                return;
            }
            if (isset($n->args) && is_array($n->args))
                foreach ($n->args as $k) $walk($k);
        };
        $walk($this);
    }

    public function push_accessibility($new, $accessibility)
    {
        if ($this->parent)
            return $this->parent->push_accessibility($new, $accessibility);
    }

    public function push_arithmetic($token)
    {
        global $token2classname;
        return $this->push_binary($token2classname[$token]);
    }
    public function push_attr($caret)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_binary($func)
    {
        if ($parent = $this->parent) {
            if ($func::$input_priority > $parent->stack_priority) {
                $level = $this->level;
                $new = new LeanCaret($this->indent, $level);
                $parent->replace($this, new $func($this, $new, $this->indent, $level));
                return $new;
            }
            return $parent->push_binary($func);
        }
    }

    public function push_block_comment($comment, $docstring)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_left($func, $prev_token)
    {
        switch ($func) {
            case 'LeanParenthesis':
            case 'LeanBracket':
            case 'LeanBrace':
            case 'LeanAngleBracket':
            case 'LeanFloor':
            case 'LeanCeil':
            case 'LeanNorm':
            case 'LeanDoubleAngleQuotation':
            case 'LeanSingleAngleQuotation':
                $indent = $this->indent;
                $level = $this->level;
                $caret = new LeanCaret($indent, $level);
                if ($func == 'LeanBracket') {
                    if ($prev_token == ' ') {
                        # consider the case: a ≡ b [MOD n]
                        $self = $this;
                        $parent = $self->parent;
                        while ($parent) {
                            if ($parent instanceof Lean_equiv || $parent instanceof LeanNotEquiv) {
                                $level = $self->level;
                                $new = new $func($caret, $indent, $level);
                                $parent->replace($self, new LeanArgsSpaceSeparated([$self, $new], $indent, $level));
                                return $caret;
                            }
                            $self = $parent;
                            $parent = $parent->parent;
                        }
                    } elseif (
                        $this instanceof LeanToken || 
                        $this instanceof LeanProperty || 
                        $this instanceof LeanGetElem || $this instanceof LeanGetElemQue || $this instanceof LeanGetElemQuote || 
                        $this instanceof LeanUnaryArithmeticPost || 
                        $this instanceof LeanBracket ||
                        $this instanceof LeanPairedGroup && $this->is_Expr()
                    ) {
                        $this->parent->replace($this, new LeanGetElem($this, $caret, $indent, $level));
                        return $caret;
                    }
                }
                $new = new $func($caret, $indent, $level);
                if ($this->parent instanceof LeanArgsSpaceSeparated)
                    $this->parent->push($new);
                else
                    $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent, $level));
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function push_line_comment($comment)
    {
        return $this->parent->push_line_comment($comment);
    }

    public function push_minus()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_multiple($func, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $func) {
            $parent->push($caret);
        } else
            $parent->replace($this, new $func([$this, $caret], $parent));

        return $caret;
    }

    public function push_or()
    {
        $parent = $this->parent;
        return Lean_lor::$input_priority > $parent->stack_priority ? $this->push_multiple("Lean_lor", new LeanCaret($this->indent, $this->level)) : $parent->push_or();
    }

    public function push_post_unary($func)
    {
        $parent = $this->parent;
        if ($func::$input_priority > $parent->stack_priority) {
            $new = new $func($this, $this->indent, $this->level);
            $parent->replace($this, $new);
            return $new;
        } else
            return $parent->push_post_unary($func);
    }

    public function push_quote($quote)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_right($func)
    {
        if ($this->parent)
            return $this->parent->push_right($func);
    }

    public function push_token($word)
    {
        return $this->append(new LeanToken($word, $this->indent, $this->level), "token");
    }

    public function regexp()
    {
        return [];
    }

    public function relocate_last_comment() {}

    public function set_line($line)
    {
        $this->line = $line;
        return $line;
    }

    public function split(&$syntax = null)
    {
        return [$this];
    }
    public function strArgs()
    {
        return $this->args;
    }

    public function tokens_space_separated()
    {
        return [];
    }

    public function toLatex(&$syntax = null)
    {
        $format = $this->latexFormat();
        $args = $this->latexArgs($syntax);
        if ($args)
            return sprintf($format, ...$args);
        return $format;
    }

    public function toString()
    {
        $format = $this->strFormat();
        $args = $this->strArgs();
        if ($args)
            return sprintf($format, ...$args);
        return $format;
    }

    public function traverse()
    {
        yield $this;
    }

}

// END OF base family (LeanMethodChaining stays in lean.php)
