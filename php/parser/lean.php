<?php
require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/../itertools.php';
require_once dirname(__file__) . '/newline_skipping_comment.php';

ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'LeanAdd',
    '-' => 'LeanSub',
    '*' => 'LeanMul',
    '/' => 'LeanDiv',
    '÷' => 'LeanEDiv',  // euclidean division
    '//' => 'LeanFDiv', // floor division
    '%' => 'LeanModular',
    '×' => 'Lean_times',
    '@' => 'LeanMatMul',
    '•' => 'Lean_bullet',
    '⬝' => 'Lean_cdotp',
    '∘' => 'Lean_circ',
    '▸' => 'Lean_blacktriangleright',
    '⊙' => 'Lean_odot',
    '⊕' => 'Lean_oplus',
    '⊖' => 'Lean_ominus',
    '⊗' => 'Lean_otimes',
    '⊘' => 'Lean_oslash',
    '⊚' => 'Lean_circledcirc',
    '⊛' => 'Lean_circledast',
    '⊜' => 'Lean_circleeq',
    '⊝' => 'Lean_circleddash',
    '⊞' => 'Lean_boxplus',
    '⊟' => 'Lean_boxminus',
    '⊠' => 'Lean_boxtimes',
    '⊡' => 'Lean_dotsquare',
    '∈' => 'Lean_in',
    '∉' => 'Lean_notin',
    '|' => 'LeanBitOr',
    '&' => 'LeanBitAnd',
    '||' => 'LeanLogicOr',
    '|||' => 'LeanBitwiseOr',
    '&&' => 'LeanLogicAnd',
    '&&&' => 'LeanBitwiseAnd',
    '^' => 'LeanPow',
    '^^' => 'LeanLogicXor',
    '^^^' => 'LeanBitwiseXor',
    '<' => 'Lean_lt',
    '<<' => 'Lean_ll',
    '<<<' => 'Lean_lll',
    '<=' => 'Lean_le',
    '>' => 'Lean_gt',
    '>>' => 'Lean_gg',
    '>>>' => 'Lean_ggg',
    '>=' => 'Lean_ge',
    '∨' => 'Lean_lor',
    '∧' => 'Lean_land',
    '∪' => 'Lean_cup',
    '∩' => 'Lean_cap',
    "\\" => 'Lean_setminus',
    '|>.' => 'LeanMethodChaining',
    '<|' => 'Lean_lazy',
    '⊆' => 'Lean_subseteq',
    '⊂' => 'Lean_subset',
    '⊇' => 'Lean_supseteq',
    '⊃' => 'Lean_supset',
    '⊔' => 'Lean_sqcup',
    '⊓' => 'Lean_sqcap',
    '++' => 'LeanAppend',
    '→' => 'Lean_rightarrow',
    '↦' => 'Lean_mapsto',
    '↔' => 'Lean_leftrightarrow',
    '≠' => 'Lean_ne',
    '≡' => 'Lean_equiv',
    '≢' => 'LeanNotEquiv',
    '≍' => 'Lean_asymp',
    '≃' => 'Lean_simeq',
    '≈' => 'Lean_approx',
    '∣' => 'LeanDvd',
];

preg_match_all("/'(\w+)'/", file_get_contents(dirname(__FILE__) . '/../../static/codemirror/mode/lean/tactics.js'), $tactics);
[, $tactics] = $tactics;

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

class LeanCaret extends Lean
{
    public function append($new, $func)
    {
        if (is_string($new)) {
            $this->parent->replace($this, new $new($this, $this->indent, $this->level));
            return $this;
        } else {
            $this->parent->replace($this, $new);
            return $new;
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanArgsNewLineSeparated;
    }

    public function is_outsider()
    {
        return true;
    }
    public function jsonSerialize(): mixed
    {
        return "";
    }

    public function latexFormat()
    {
        return "";
    }

    public function push_accessibility($new, $accessibility)
    {
        $this->parent->replace($this, new $new($accessibility, $this, $this->indent, $this->level));
        return $this;
    }

    public function push_block_comment($comment, $docstring)
    {
        $parent = $this->parent;
        $func = $docstring ? 'LeanDocString' : 'LeanBlockComment';
        $parent->replace($this, new $func($comment, $this->indent, $this->level));
        $parent->push($this);
        return $this;
    }

    public function push_left($func, $prev_token)
    {
        $this->parent->replace($this, new $func($this, $this->indent, $this->level));
        return $this;
    }

    public function push_line_comment($comment)
    {
        $parent = $this->parent;
        $new = new LeanLineComment($comment, $this->indent, $this->level);
        $parent->replace($this, $new);
        return $new;
    }

    public function strFormat()
    {
        return '';
    }

}

class LeanToken extends Lean
{
    public $text;
    public $cache = null;

    static $subscript = [
        'ₐ' => 'a',
        'ₑ' => 'e',
        'ₕ' => 'h',
        'ᵢ' => 'i',
        'ⱼ' => 'j',
        'ₖ' => 'k',
        'ₗ' => 'l',
        'ₘ' => 'm',
        'ₙ' => 'n',
        'ₒ' => 'o',
        'ₚ' => 'p',
        'ᵣ' => 'r',
        'ₛ' => 's',
        'ₜ' => 't',
        'ᵤ' => 'u',
        'ᵥ' => 'v',
        'ₓ' => 'x',
        '₀' => '0',
        '₁' => '1',
        '₂' => '2',
        '₃' => '3',
        '₄' => '4',
        '₅' => '5',
        '₆' => '6',
        '₇' => '7',
        '₈' => '8',
        '₉' => '9',
        'ᵦ' => '\beta',
        'ᵧ' => '\gamma',
        'ᵨ' => '\rho',
        'ᵩ' => '\phi',
        'ᵪ' => '\chi',
    ];

    static $subscript_keys = null;
    static $supscript = [
        '⁰' => '0',
        '¹' => '1',
        '²' => '2',
        '³' => '3',
        '⁴' => '4',
        '⁵' => '5',
        '⁶' => '6',
        '⁷' => '7',
        '⁸' => '8',
        '⁹' => '9',
        'ᵅ' => 'alpha',
        'ᵝ' => 'beta',
        'ᵞ' => 'gamma',
        'ᵟ' => 'delta',
        'ᵋ' => 'epsilon',
        'ᵑ' => 'eta',
        'ᶿ' => 'theta',
        'ᶥ' => 'iota',
        'ᶺ' => 'lambda',
        'ᵚ' => 'omega',
        'ᶹ' => 'upsilon',
        'ᵠ' => 'phi',
        'ᵡ' => 'chi',
    ];
    static $supscript_keys = null;
    public function __construct($text, $indent, $level, $parent = null)
    {
        parent::__construct($indent, $level, $parent);
        $this->text = $text;
    }

    /** Mark this occurrence as a free random variable (red LaTeX rendering). */
    public function setRandomVariable()
    {
        $this->kwargs['isRandomVariable'] = true;
    }

    public function append($new, $func)
    {
        if ($this->parent)
            return $this->parent->insert($this, $new, $func);
    }

    public function ends_with_2_letters()
    {
        return preg_match("/[a-zA-Z]{2,}$/", $this->text);
    }

    public function equals($other) {
        if ($other instanceof LeanToken)
            return $this->text == $other->text;
    }
    public function is_parallel_operator() {
        return preg_match("/_\?+$/", $this->text);
    }

    public function isProp($vars)
    {
        return ($vars[$this->text] ?? null) == 'Prop';
    }

    public function is_TypeStar() {
        // implicit universe variable
        switch ($this->text) {
            case 'Sort':
            case 'Type':
            case 'ℝ':
                return true;
        }
    }

    public function is_variable()
    {
        return std\fullmatch('/[a-zA-Z_][a-zA-Z_0-9]*/', $this->text);
    }

    public function jsonSerialize(): mixed
    {
        return $this->text;
    }

    public function latexFormat()
    {
        $text = escape_specials($this->text);
        if ($text == $this->text) {
            $text = preg_replace_callback(
                LeanToken::$subscript_keys,
                fn($m) => '_{' . strtr($m[0], LeanToken::$subscript) . '}',
                $text
            );

            $text = preg_replace_callback(
                LeanToken::$supscript_keys,
                fn($m) => '^{' . strtr($m[0], LeanToken::$supscript) . '}',
                $text
            );
            if (str_starts_with($text, '_'))
                $text = '\\' . $text;
        }
        if (!empty($this->kwargs['isRandomVariable']))
            return '{\\color{red} {' . $text . '}}';
        return $text;
    }

    public function lower()
    {
        $this->text = strtolower($this->text);
        return $this;
    }

    public function operand_count() {
        preg_match("/\?*$/", $this->text, $m);
        return strlen($m[0]);
    }
    public function push_quote($quote)
    {
        $this->text .= $quote;
        return $this;
    }

    public function push_token($word)
    {
        $level = $this->level;
        $new = new LeanToken($word, $this->indent, $level);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent, $level));
        return $new;
    }

    public function regexp()
    {
        return ["_"];
    }
    public function starts_with_2_letters()
    {
        return preg_match("/^[a-zA-Z]{2,}/", $this->text);
    }

    public function strFormat()
    {
        return $this->text;
    }

    public function tactic_block_info() {
        $map = [];
        $map[0][] = $this;
        $this->cache['size'] = 1;
        return $map;
    }

    public function tokens_space_separated()
    {
        return [$this];
    }

}

LeanToken::$subscript_keys = '/[' . implode('', array_keys(LeanToken::$subscript)) . ']+/u';
LeanToken::$supscript_keys = '/[' . implode('', array_keys(LeanToken::$supscript)) . ']+/u';

class LeanLineComment extends Lean
{
    public $text;

    public function __construct($text, $indent, $level, $parent = null)
    {
        parent::__construct($indent, $level, $parent);
        $this->text = $text;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '--';
            case 'command':
                return '%';
            default:
                return parent::__get($vname);
        }
    }

    public function is_comment()
    {
        return true;
    }
    public function is_indented()
    {
        switch ($this->text) {
            case 'given':
                if (($parent = $this->parent) instanceof LeanArgsNewLineSeparated &&
                    ($parent = $parent->parent) instanceof LeanArgsIndented &&
                    ($parent = $parent->parent) instanceof LeanColon &&
                    ($parent = $parent->parent) instanceof LeanAssign &&
                    $parent->parent instanceof Lean_lemma
                )
                    return false;
                break;

            case 'proof';
                if (($parent = $this->parent) instanceof LeanStatements) {
                    if ($parent->parent instanceof LeanBy)
                        $parent = $parent->parent;
                    if (($parent = $parent->parent) instanceof LeanAssign && $parent->parent instanceof Lean_lemma)
                        return false;
                } elseif (($parent = $this->parent) instanceof LeanArgsNewLineSeparated) {
                    if (($parent = $parent->parent) instanceof LeanAssign && $parent->parent instanceof Lean_lemma)
                        return false;
                }
            case 'imply':
                if (($parent = $this->parent) instanceof LeanStatements &&
                    ($parent = $parent->parent) instanceof LeanColon &&
                    ($parent = $parent->parent) instanceof LeanAssign &&
                    $parent->parent instanceof Lean_lemma
                )
                    return false;
                break;
            default:
                if ($this->parent instanceof LeanTactic)
                    return false;
        }
        return true;
    }
    public function is_outsider()
    {
        return preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', $this->text);
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->text];
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep$this->text";
    }

    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep$this->text";
    }

}

class LeanBlockComment extends Lean
{
    public $text;

    public function __construct($text, $indent, $level, $parent = null)
    {
        parent::__construct($indent, $level, $parent);
        $this->text = $text;
    }

    public function is_comment()
    {
        return true;
    }
    public function is_indented()
    {
        return true;
    }
    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->text];
    }

    public function sep()
    {
        return '';
    }
    public function set_line($line)
    {
        $this->line = $line;
        $line += substr_count($this->text, "\n");
        return $line;
    }

    public function strFormat()
    {
        return "/-$this->text-/";
    }

}

class LeanDocString extends LeanBlockComment
{
    public $text;

    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->text];
    }
    public function set_line($line)
    {
        $this->line = $line;
        ++$line;
        $line += substr_count($this->text, "\n");
        ++$line;
        return $line;
    }
    public function strFormat()
    {
        return "/--\n$this->text\n-/";
    }

}


trait LeanMultipleLine
{
    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line) + 1;
        }
        return $line - 1;
    }
}

abstract class LeanArgs extends Lean
{
    public static $input_priority = 47;
    public function __clone()
    {
        parent::__clone();
        $this->args = array_map(fn($arg) => clone $arg, $this->args);
        foreach ($this->args as $arg) {
            $arg->parent = $this;
        }
    }

    public function __construct($args, $indent, $level, $parent = null)
    {
        parent::__construct($indent, $level, $parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return "\\$this->func";
            case 'func':
                return preg_replace('/^Lean_?/', '', get_class($this));
            default:
                return parent::__get($vname);
        }
    }

    public function insert_calc($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanCalc($caret, $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $func)
    {
        if ($caret instanceof LeanCaret) {
            $this->replace($caret, new LeanTactic($func, $caret, $this->indent, $caret->level));
            return $caret;
        }
        return $this->insert_word($caret, $func);
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function push_args_indented($indent, $newline_count, $function_call = true) {
        $end = end($this->args);
        if (!$function_call || $end instanceof LeanToken || $end instanceof LeanProperty || $end instanceof LeanParenthesis) {
            $caret = new LeanCaret($indent, $end->level);
            $new = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
            $caret = $new->push_newlines($newline_count - 1);
            $this->replace($end, new LeanArgsIndented($end, $new, $this->indent, $caret->level));
            return $caret;
        }
    }
    public function regexp()
    {
        $func = ucfirst($this->func);
        $args = array_map(fn($arg) => [...$arg->regexp(), "_"], $this->args);
        $regexp = [];
        foreach (itertools\product($args) as $list) {
            $expr = implode("", $list);
            $regexp[] = "$func$expr";
        }
        return $regexp;
    }

    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line);
        }
        return $line;
    }

    public function strip_parenthesis()
    {
        return array_map(fn($arg) => $arg instanceof LeanParenthesis && !($arg->arg instanceof LeanMethodChaining || $arg->arg instanceof Lean_rightarrow || $arg->arg instanceof LeanColon) ? $arg->arg : $arg, $this->args);
    }

    public function traverse()
    {
        yield $this;
        foreach ($this->args as $arg) {
            if ($arg != null)
                yield from $arg->traverse();
        }
    }

}

# Frac|Abs|Norm|Length|Sign|Square|Sqrt|Floor|Ceil|Sin|Cos|Tan|Cot|Arg|Neg|Inv|Cast|Coe|Exp|Log|Val|Card|ToNat|Arccos|Arcsin|Arctan|Arccot|Re|Im|Succ
abstract class LeanUnary extends LeanArgs
{
    public static $input_priority = 47;
    public function __construct($arg, $indent, $level, $parent = null)
    {
        parent::__construct([], $indent, $level, $parent);
        $this->arg = $arg;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'arg':
                return $this->args[0];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'arg':
                $this->args[0] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert_if($caret)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->arg = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function jsonSerialize(): mixed
    {
        return $this->arg->jsonSerialize();
    }

    public function replace($old, $new)
    {
        assert($this->arg === $old, new Exception("assert failed: public function replace(\$old, \$new)"));
        $this->arg = $new;
    }

}

require_once dirname(__FILE__) . '/lean/paired.php';

abstract class LeanBinary extends LeanArgs
{
    public static $input_priority = 47;

    public function __construct($lhs, $rhs, $indent, $level, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'lhs':
                return $this->args[0];
            case 'rhs':
                return $this->args[1];
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'lhs':
                $this->args[0] = $val;
                break;
            case 'rhs':
                $this->args[1] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    public function insert_if($caret)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->rhs = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $func)
    {
        // consider the case where `case` is a tactic within (LeanColon/LeanAdd):
        // (h : arg x + arg y ∈ Ioc (-Real.pi) Real.pi) :
        return $this->insert_word($caret, $func);
    }
    public function jsonSerialize(): mixed
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
    }

    public function latexFormat()
    {
        return "{%s} $this->command {%s}";
    }

    abstract public function sep();

    public function set_line($line)
    {
        $this->line = $line;
        $line = $this->lhs->set_line($line);
        $sep = $this->sep();
        if ($sep && $sep[0] == "\n")
            ++$line;
        return $this->rhs->set_line($line);
    }

}

/**
 * Interval notation `a..b` used by `∫ x in a..b, f x` (Mathlib `notation3 "a".."b"`).
 * Binds looser than arithmetic/relational nodes, matching the term-level parsing of the bounds.
 */
class LeanUpto extends LeanBinary
{
    public static $input_priority = 49; // LeanRelational::$input_priority - 1

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '..';
            default:
                return parent::__get($vname);
        }
    }

    public function sep()
    {
        return '';
    }

    public function strFormat()
    {
        return '%s..%s';
    }

    public function latexFormat()
    {
        return '%s..%s';
    }
}

class LeanProperty extends LeanBinary
{
    public static $input_priority = 81; // LeanPow::$input_priority + 1
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 87;
            case 'operator':
            case 'command':
                return '.';
            default:
                return parent::__get($vname);
        }
    }

    public function equals($other) {
        if ($other instanceof LeanProperty)
            return $this->lhs->equals($other->lhs) && $this->rhs->equals($other->rhs);
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                if (str_starts_with($func, 'Lean_'))
                    $caret = $this->insert_word($caret, substr($func, 5));
            } elseif ($type == 'modifier') {
                return $this->parent->insert($this, $func, $type);
            } else {
                $caret = new LeanCaret($this->indent, $caret->level);
                $this->parent->replace(
                    $this,
                    new LeanArgsSpaceSeparated(
                        [
                            $this,
                            new $func($caret, $caret->indent, $caret->level)
                        ],
                        $this->indent, $caret->level
                    )
                );
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_left($caret, $func, $prev_token = '')
    {
        if ($func == 'LeanDoubleAngleQuotation')
            return $caret->push_left($func, $prev_token);
        if ($this->parent)
            return $this->parent->insert_left($this, $func, $prev_token);
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->parent instanceof LeanTactic && $indent > $this->indent)
            return $this->parent->push_args_indented($indent, $newline_count, false);
        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }

    public function insert_unary($caret, $func)
    {
        if ($this->parent)
            return $this->parent->insert_unary($this, $func);
    }

    public function insert_word($caret, $word)
    {
        if ($caret instanceof LeanCaret)
            return parent::insert_word($caret, $word);
        if ($this->parent)
            return $this->parent->insert_word($this, $word);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            ($parent instanceof LeanArgsIndented && $parent->rhs === $this) ||
            ($parent instanceof LeanIte && $parent->else === $this);
    }

    public function isProp($vars)
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LeanToken) {
            switch ($rhs->text) {
                case 'Infinite':
                case 'Infinitesimal':
                case 'InfinitePos':
                case 'InfiniteNeg':
                    return true;
            }
        }
    }
    public function is_space_separated()
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LeanToken) {
            $command = $rhs->text;
            switch ($command) {
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    return true;
            }
        }
    }
    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($rhs instanceof LeanToken) {
            switch ($rhs->text) {
                case 'exp':
                    $arg = '%s';
                    if ($lhs instanceof LeanToken) {
                        switch ($lhs->text) {
                            case 'Real':
                            case 'Complex':
                            case 'Exp':
                                $arg = null;
                        }
                    }
                    if ($arg) {
                        $exponent = $this->lhs;
                        if ($exponent instanceof LeanParenthesis) {
                            $exponent = $exponent->arg;
                        }
                        return [$exponent->toLatex($syntax)];
                    }
                    break;
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    $arg = '%s';
                    if ($lhs instanceof LeanToken) {
                        switch ($lhs->text) {
                            case 'Real':
                            case 'Complex':
                            case 'Cos':
                            case 'Sin':
                            case 'Tan':
                            case 'Log':
                                $arg = null;
                        }
                    }
                    if ($arg)
                        return [$this->lhs->toLatex($syntax)];
                    break;
                case 'fmod':
                    return [$this->lhs->toLatex($syntax)];
                case 'card':
                    if (!($this->lhs instanceof LeanToken && $this->parent instanceof LeanArgsSpaceSeparated && $this->parent->args[0] === $this)) {
                        $arg = $this->lhs;
                        if ($arg instanceof LeanParenthesis && !($arg->arg instanceof LeanColon))
                            $arg = $arg->arg;
                        return [$arg->toLatex($syntax)];
                    }
                    break;
                case 'softmax':
                    $syntax['softmax'] = true;
                    break;
                case 'sigmoid':
                    return [$this->lhs->toLatex($syntax)];
                case 'factorial':
                    return [$this->lhs->toLatex($syntax)];
                case 'det':
                    $arg = $this->lhs;
                    if ($arg instanceof LeanParenthesis && !($arg->arg instanceof LeanColon))
                        $arg = $arg->arg;
                    return [$arg->toLatex($syntax)];
            }
        }
        return parent::latexArgs($syntax);
    }
    public function latexFormat()
    {
        [$lhs, $rhs] = $this->args;
        if ($rhs instanceof LeanToken) {
            $command = $rhs->text;
            switch ($command) {
                case 'exp':
                    $arg = '%s';
                    if ($lhs instanceof LeanToken) {
                        switch ($lhs->text) {
                            case 'Real':
                            case 'Complex':
                            case 'Exp':
                                $arg = null;
                        }
                    }
                    if ($arg)
                        return '{\color{RoyalBlue} e} ^ {%s}';
                    break;
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    $arg = '%s';
                    if ($lhs instanceof LeanToken) {
                        switch ($lhs->text) {
                            case 'Real':
                            case 'Complex':
                            case 'Cos':
                            case 'Sin':
                            case 'Tan':
                            case 'Log':
                                $arg = null;
                        }
                    }
                    if ($arg)
                        return "\\$command {%s}";
                    break;
                case 'fmod':
                    return '{%s} {\color{red}\%%}';
                case 'card':
                    if (!($this->lhs instanceof LeanToken && $this->parent instanceof LeanArgsSpaceSeparated && $this->parent->args[0] === $this))
                        return '\left|{%s}\right|';
                case 'epsilon':
                    if ($this->lhs instanceof LeanToken && $this->lhs->text == 'Hyperreal')
                        return '0^+';
                case 'omega':
                    if ($this->lhs instanceof LeanToken && $this->lhs->text == 'Hyperreal')
                        return '\infty';
                case 'sigmoid':
                    return '{\\color{RoyalBlue}\\sigma}\\left(%s\\right)';
                case 'factorial':
                    return '{%s}!';
                case 'det':
                    return '\left|{%s}\right|';
            }
        }
        return "{%s}$this->command{%s}";
    }

    public function push_attr($caret)
    {
        return parent::push_attr($caret);
    }

    public function push_token($word)
    {
        $level = $this->level;
        $new = new LeanToken($word, $this->indent, $level);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent, $level));
        return $new;
    }

    public function regexp()
    {
        $func = ucfirst("$this->rhs");
        $regexp = $this->lhs->regexp();
        $regexp = array_map(fn($expr) => "$func$expr", $regexp);
        $regexp[] = "{$func}_";
        return $regexp;
    }

    public function sep()
    {
        return '';
    }
    public function strFormat()
    {
        return "%s$this->operator%s";
    }

}

class LeanColon extends LeanBinary
{
    public static $input_priority = 19;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return ':';
            default:
                return parent::__get($vname);
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret && $indent > $this->indent) {
                $caret->indent = $indent;
                $this->rhs = new LeanStatements([$caret], $indent, $caret->level);
                return $caret;
            }
            if ($caret instanceof LeanStatements && $indent == $this->indent && $this->parent instanceof LeanParenthesis)
                return $caret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
    public function is_indented()
    {
        return false;
    }
    public function peelLatexCoe()
    {
        return $this->lhs->peelLatexCoe();
    }

    public function tensorTypeShape()
    {
        $ty = $this->rhs;
        if ($ty instanceof LeanParenthesis)
            $ty = $ty->arg;
        if (!$ty instanceof LeanArgsSpaceSeparated)
            return null;
        $args = array_values(array_filter($ty->args, fn($a) => !$a instanceof LeanCaret));
        if (count($args) < 2)
            return null;
        $head = $args[0];
        if (!$head instanceof LeanToken || $head->text !== 'Tensor')
            return null;
        $shape = $args[count($args) - 1];
        if ($shape instanceof LeanBracket) {
            $inner = $shape->arg;
            if (!$inner || $inner instanceof LeanCaret)
                return [];
            if ($inner instanceof LeanArgsCommaSeparated)
                return array_values(array_filter($inner->args, fn($a) => !$a instanceof LeanCaret));
            return [$inner];
        }
        return [$shape];
    }

    public function isZeroOneTensor()
    {
        $lhs = $this->lhs;
        return $lhs instanceof LeanToken && ($lhs->text === '0' || $lhs->text === '1') && $this->tensorTypeShape() !== null;
    }

    public function latexFormat()
    {
        if ($this->isZeroOneTensor())
            return '\\mathbf{' . $this->lhs->text . '}_{%s}';
        return parent::latexFormat();
    }

    public function latexArgs(&$syntax = null)
    {
        if ($this->isZeroOneTensor()) {
            $dims = $this->tensorTypeShape();
            return [implode(',', array_map(fn($d) => $d->toLatex($syntax), $dims))];
        }
        return parent::latexArgs($syntax);
    }
    public function sep()
    {
        $rhs = $this->rhs;
        return $rhs instanceof LeanStatements ? "\n" : ($rhs instanceof LeanCaret || $this->parent instanceof LeanGetElem ? '' : ' ');
    }

    public function strArgs()
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanArgsNewLineSeparated) {
            $args = array_map(fn($arg) => "$arg", array_slice($lhs->args, 1));
            array_unshift($args, "{$lhs->args[0]}");
            $lhs = implode("\n", $args);
        }
        return [$lhs, $rhs];
    }

    public function strFormat()
    {
        $sep = $this->sep();
        $first = "%s";
        if (!($this->parent instanceof LeanGetElem))
            $first .= " ";
        return "$first$this->operator$sep%s";
    }

}

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
        return !$parent || $parent instanceof LeanArgsNewLineSeparated || ($parent instanceof LeanArgsIndented && $parent->rhs === $this);
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

trait LeanProp
{
    public function isProp($vars)
    {
        return true;
    }
}

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

require_once dirname(__FILE__) . '/lean/relational.php';

require_once dirname(__FILE__) . '/lean/membership.php';

require_once dirname(__FILE__) . '/lean/arithmetic.php';

/** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
class Lean_lazy extends LeanBinary
{
    public static $input_priority = 20;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                // below input_priority, so a following `<|` nests on the right
                return 19;
            case 'operator':
                return '<|';
            default:
                return parent::__get($vname);
        }
    }

    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s <|{$sep}%s";
    }
}

class LeanMethodChaining extends LeanBinary
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 59;
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        return '%s\\ \texttt{|>.}%s';
    }
    public function sep()
    {
        return '';
    }

    public function strFormat()
    {
        return '%s |>.%s';
    }
}

trait LeanGetElemBase
{
    public function push_right($func)
    {
        if ($func == 'LeanBracket')
            return $this;
        return parent::push_right($func);
    }

    public function insert_comma($caret)
    {
        $new = new LeanCaret($this->indent, $caret->level);
        $this->rhs = new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level);
        return $new;
    }
}

trait LeanGetElemBaseBinary 
{
    use LeanGetElemBase;
    public function sep()
    {
        return '';
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 18;
            default:
                return parent::__get($vname);
        }
    }
}


require_once dirname(__FILE__) . '/lean/indexing.php';

class Lean_is extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'is';
            case 'command':
                return '{\color{blue}\text{is}}';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function latexFormat()
    {
        return "{%s}\\ $this->command\\ {%s}";
    }

    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

class Lean_is_not extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '{\color{blue}\text{is not}}';
            case 'operator':
                return 'is not';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

require_once dirname(__FILE__) . '/lean/logic.php';

require_once dirname(__FILE__) . '/lean/set.php';

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
        if ($this->parent instanceof LeanBrace)
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


/**
 * Semantic pass over signature binders: braces `{m : Measure T}` plus brackets
 * `[IsProbabilityMeasure m]` identify probability-space domains T, and explicit
 * binders `(v : T → U)` on such a domain are random variables.
 * @param object[] $binderRoots
 * @return string[]
 */
function collect_random_var_names(array $binderRoots)
{
    $nodes = [];
    $gather = function ($n) use (&$gather, &$nodes) {
        if (!$n || !is_object($n)) return;
        $nodes[] = $n;
        if (isset($n->args) && is_array($n->args))
            foreach ($n->args as $k) $gather($k);
    };
    foreach ($binderRoots as $r) $gather($r);

    /** @var array<string,string> measure name -> domain text */
    $measures = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanBrace)) continue;
        $cols = [];
        $a = $n->arg;
        if ($a instanceof LeanColon) $cols[] = $a;
        elseif ($a instanceof LeanArgsSpaceSeparated)
            foreach ($a->args as $c) if ($c instanceof LeanColon) $cols[] = $c;
        foreach ($cols as $col) {
            $rhs = $col->rhs->peelGroup();
            if ($rhs->headIs('Measure') && $rhs instanceof LeanArgsSpaceSeparated
                && count($rhs->args) >= 2) {
                $dom = trim((string)$rhs->args[1]->peelGroup());
                if ($dom !== '') $measures[trim((string)$col->lhs)] = $dom;
            }
        }
    }

    /** @var array<string,bool> */
    $probDomains = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanBracket)) continue;
        $a = $n->arg->peelGroup();
        if ($a instanceof LeanArgsSpaceSeparated && count($a->args) >= 2
            && $a->headIs('IsProbabilityMeasure')) {
            $m = trim((string)$a->args[1]->peelGroup());
            if (isset($measures[$m])) $probDomains[$measures[$m]] = true;
        }
    }

    /** @var array<string,bool> */
    $rvs = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanParenthesis)) continue;
        $col = $n->arg instanceof LeanColon ? $n->arg : null;
        if (!$col) continue;
        $ty = $col->rhs->peelGroup();
        if (!($ty instanceof Lean_rightarrow)) continue;
        $dom = trim((string)$ty->lhs->peelGroup());
        if (!isset($probDomains[$dom])) continue;
        $addNames = function ($x) use (&$addNames, &$rvs) {
            $y = $x->peelGroup();
            if ($y instanceof LeanToken) $rvs[$y->text] = true;
            elseif ($y instanceof LeanArgsSpaceSeparated)
                foreach ($y->args as $z) $addNames($z);
        };
        $addNames($col->lhs);
    }
    return array_keys($rvs);
}

/** Mark a statement sequence; top-level `let q := …` hides `q` thereafter. */
function mark_random_var_sequence(array $stmts, array $rvNames)
{
    $letBound = [];
    foreach ($stmts as $st)
        $st->markRandomVarNames($rvNames, $letBound);
}


class LeanModule extends LeanStatements
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                return $this;
            case 'stack_priority':
                return -3;
            default:
                return parent::__get($vname);
        }
    }

    public function array_push(&$vars, $lhs, $rhs)
    {
        if ($lhs instanceof LeanToken) {
            $args = [$lhs, $rhs];
            while (($end = end($args)) instanceof Lean_rightarrow)
                array_splice($args, count($args) - 1, 2, [$end->lhs, $end->rhs]);
            $vars[] = $args;
        } elseif ($lhs instanceof LeanArgsSpaceSeparated) {
            foreach ($lhs->args as $lhs)
                $this->array_push($vars, $lhs, $rhs);
        }
    }
    public function create_property($module) {
        return array_reduce(
            explode('.', $module),
            function ($carry, $token) {
                $token = new LeanToken($token, 0, 0);
                return $carry ? new LeanProperty($carry, $token, 0, 0) : $token;
            },
        );
    }
    public function decode(&$json, &$latex)
    {
        [[$line, $latexFormat]] = std\entries($json);
        if (isset($latex[$line])) {
            if (!is_array($latex[$line]))
                $latex[$line] = [$latex[$line]];
            $latex[$line][] = $latexFormat;
        } else
            $latex[$line] = $latexFormat;
    }

    public function echo()
    {
        $args = &$this->args;
        $this->import('sympy.printing.echo');
        for ($index = 0; $index < count($args); ++$index)
            $args[$index]->echo();
    }
    public function echo2vue($leanFile)
    {
        $this->relocate_last_comment();
        $this->echo();
        $leanEchoFile = preg_replace('/\.lean$/', '.echo.lean', $leanFile);
        if (!file_exists($leanEchoFile)) {
            error_log("create new lean file = $leanEchoFile");
            std\createNewFile($leanEchoFile);
        }
        // create a block to write the code
        {
            $file = new std\Text($leanEchoFile);
            $codeStr = "$this";
            $file->writelines([$codeStr]);
        }

        chdir(dirname(dirname(dirname(__FILE__))));
        $imports = array_filter(
            $this->args,
            fn($import) =>
            $import instanceof Lean_import &&
                str_starts_with($package = "$import->arg", 'Lemma.') &&
                (
                    !file_exists($olean = ".lake/build/lib/lean/" . ($module = str_replace('.', '/', $package)) . ".olean") || 
                    filemtime($olean) < filemtime($module. ".lean")
                )
        );
        $lakePath = get_lake_path();
        if ($imports) {
            $imports = implode(' ', array_map(fn($import) => "$import->arg", $imports));
            $cmd = "$lakePath build $imports";
            // $cmd = $lakePath . " setup-file \"$leanEchoFile\"";
            error_log("executing cmd = $cmd");
            if (std\is_linux())
                shell_exec($cmd);
            else
                std\exec($cmd, $_, get_lean_env());
        }
        // 10000 heartbeats approximates 1 second
        $cmd = $lakePath . ' env lean -D"linter.unusedTactic=false" -D"linter.dupNamespace=false" -D"diagnostics.threshold=1000" -D"maxHeartbeats=4000000" '. std\escapeshellarg($leanEchoFile);
        if (std\is_linux())
            exec($cmd, $output_array);
        else
            std\exec($cmd, $output_array, get_lean_env());
        $latex = [];
        $error = [];
        $this->set_line(1);
        $end = end($this->args);
        if ($end->line != substr_count($codeStr, "\n") + 1) {
            $error[] = [
                'code' => '',
                'line' => $end->line,
                'type' => 'error',
                'info' => 'the line count of *.echo.lean file is not correct'
            ];
        }
        foreach ($output_array as $jsonline) {
            $json = std\decode($jsonline);
            if ($json)
                $this->decode($json, $latex);
            elseif (preg_match('#([/\w]+)\.lean:(\d+):(\d+): (\w+): (.+)#', $jsonline, $matches)) {
                $line = intval($matches[2]);
                $col = intval($matches[3]);
                if (!isset($echo_codes))
                    $echo_codes = file($leanEchoFile);
                $code = $echo_codes[$line - 1];
                $type = $matches[4];
                $info = $matches[5];
                $error[] = [
                    'code' => $code,
                    'line' => $line, // later I will adjust this value.
                    'col' => $col - 2,
                    'type' => $type,
                    'info' => $info
                ];
            } else
                $error[count($error) - 1]['info'] .= "\n" . $jsonline;
        }

        foreach ($this->traverse() as $node) {
            if ($node instanceof LeanTactic && $node->func == 'echo')
                if (is_int($node->line)) {
                    if (!array_key_exists($node->line, $latex))
                        $latex[$node->line] = null;
                    $node->line = $latex[$node->line];
                } else {
                    error_log("unexpected node = $node");
                }
        }

        $keys = array_keys($latex);
        $indicesToDelete = [];
        foreach (std\range(count($error)) as $i) {
            $err = &$error[$i];
            $line = &$err['line'];
            $code = &$err['code'];
            if (preg_match("/^ +echo /", $code)) {
                if ($err['type'] == 'error' && $err['info'] == "No goals to be solved")
                    $code = $echo_codes[$line];
                else {
                    $indicesToDelete[] = $i;
                    continue;
                }
            }
            $line -= count(array_filter($keys, fn($key) => $key < $line)) + 1;
        }
        if ($indicesToDelete) {
            foreach (array_reverse($indicesToDelete) as $i)
                array_splice($error, $i, 1);
        }

        array_shift($this->args);
        $codes = $this->render2vue(true);
        array_push($codes['meta']['error'], ...$error);
        return $codes;
    }

    public function import($module)
    {
        $this->unshift(new Lean_import($this->create_property($module), 0, 0));
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->push(new $func($caret, $this->indent, $caret->level));
                return $caret;
            }
        }
        return $caret;
    }

    public function parse_vars($implicit)
    {
        $vars = [];
        foreach ($implicit as $brace) {
            if ($brace instanceof LeanBrace) {
                $colon = $brace->arg;
                if ($colon instanceof LeanColon)
                    $this->array_push($vars, ...$colon->args);
            }
        }
        $kwargs = [];
        foreach ($vars as $var) {
            std\setitem(
                $kwargs,
                ...array_map(fn($arg) => "$arg", $var)
            );
        }
        return $kwargs;
    }

    public function parse_vars_default($default)
    {
        $vars = [];
        foreach ($default as $parenthesis) {
            if ($parenthesis instanceof LeanParenthesis) {
                $colon = $parenthesis->arg;
                if ($colon instanceof LeanColon)
                    $this->array_push($vars, ...$colon->args);
            }
        }
        return $vars;
    }

    public function render2vue($echo, &$modify = null, &$syntax = null)
    {
        if (!$echo)
            $this->relocate_last_comment();
        $import = [];
        $open = [];
        $set_option = [];
        $preamble = [];
        $lemma = [];
        $date = [];
        $error = [];
        $comment = null;
        foreach ($this->args as $stmt) {
            if ($stmt instanceof Lean_import)
                $import[] = "$stmt->arg";
            elseif ($stmt instanceof Lean_lemma) {
                if ($stmt->assignment instanceof LeanAssign) {
                    $accessibility = $stmt->accessibility;
                    $declspec = $stmt->assignment->lhs;
                    if ($declspec instanceof LeanColon) {
                        if ($attribute = $stmt->attribute) {
                            $attribute = $attribute->arg;
                            if ($attribute instanceof LeanBracket) {
                                $attribute = $attribute->arg;
                                if ($attribute instanceof LeanArgsCommaSeparated)
                                    $attribute = array_map(fn($arg) => "$arg", $attribute->args);
                                elseif ($attribute instanceof LeanToken)
                                    $attribute = ["$attribute"];
                            }
                        }
                        $imply = $declspec->rhs->args;
                        if ($imply[0] instanceof LeanLineComment && $imply[0]->text == 'imply')
                            array_shift($imply);

                        // semantic pass: random variables are explicit binders
                        // on a probability-space domain; mark their free
                        // occurrences in the signature and imply statements
                        $rvNames = collect_random_var_names([$declspec->lhs]);
                        if ($rvNames) {
                            $declspec->lhs->markRandomVarNames($rvNames);
                            mark_random_var_sequence($imply, $rvNames);
                        }

                        $proof = $stmt->assignment->rhs;
                        $by = $proof instanceof LeanBy ? 'by' : ($proof instanceof LeanCalc ? 'calc' : '');
                        $implyLean = preg_replace("/^  /m", "", implode("\n", array_map(fn($stmt) => "$stmt", $imply)));

                        if (count($imply) > 1 && ($imply[0] instanceof Lean_let)) {
                            $implyLatex = implode(
                                "\\\\\n",
                                array_map(
                                    function ($stmt) use (&$syntax) {
                                        return "&" . $stmt->toLatex($syntax) . "&& ";
                                    },
                                    $imply
                                )
                            );
                            $implyLatex = "\\begin{align*}\n$implyLatex\n\\end{align*}";
                        } else
                            $implyLatex = implode(
                                "\n",
                                array_map(
                                    function ($stmt) use (&$syntax) {
                                        return $stmt->toLatex($syntax);
                                    },
                                    $imply
                                )
                            );
                        $assignment = ' :=' . ($by ? " $by" : '');
                        $implyLatex .= "\\tag*{{$assignment}}";

                        $implyLean .= $assignment;
                        $imply = ['lean' => $implyLean, 'latex' => $implyLatex];

                        $declspec = $declspec->lhs;
                        if ($declspec instanceof LeanToken || $declspec instanceof LeanProperty) {
                            $name = $declspec;
                            $declspec = [];
                        } else {
                            [$name, $declspec] = $declspec->args;
                            $declspec = $declspec->args;
                        }

                        $instImplicit = [];
                        $implicit = [];
                        $explicit = [];
                        $given = null;
                        $default = [];
                        $decidables = [];
                        $flattened = [];
                        foreach ($declspec as $s) {
                            if ($s instanceof LeanArgsSpaceSeparated) {
                                $hasParen = false;
                                foreach ($s->args as $a)
                                    if ($a instanceof LeanParenthesis) {
                                        $hasParen = true;
                                        break;
                                    }
                                if ($hasParen) {
                                    foreach ($s->args as $a)
                                        $flattened[] = $a;
                                    continue;
                                }
                            }
                            $flattened[] = $s;
                        }
                        $declspec = $flattened;
                        foreach ($declspec as $i => &$stmt) {
                            if ($stmt instanceof LeanBracket) {
                                $instImplicit[] = "$stmt";
                                if ($stmt->arg instanceof LeanArgsSpaceSeparated) {
                                    if (count($stmt->arg->args) == 2) {
                                        [$lhs, $rhs] = $stmt->arg->args;
                                        if ($lhs instanceof LeanToken && $lhs->text == 'Decidable' && $rhs instanceof LeanToken)
                                            $decidables[] = "$rhs";
                                    }
                                }
                            } elseif ($stmt instanceof LeanBrace) {
                                $stmt->toLatex($syntax);
                                $implicit[] = $stmt;
                            } elseif ($stmt instanceof LeanArgsSpaceSeparated) {
                                if ($stmt->args[0] instanceof LeanBracket)
                                    $instImplicit[] = "$stmt";
                                elseif ($stmt->args[0] instanceof LeanBrace)
                                    $implicit[] = $stmt;
                                else
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "lemma $name is not well-defined",
                                        'type' => 'linter'
                                    ];
                            } elseif ($stmt instanceof LeanLineComment) {
                                if ($stmt->text == 'given') {
                                    $given = $i + 1;
                                    break;
                                }
                                if ($implicit)
                                    $implicit[] = "$stmt";
                                else
                                    $instImplicit[] = "$stmt";
                            } elseif ($stmt instanceof LeanParenthesis) {
                                // the given comment is missing, try to add one
                                if ($stmt->arg instanceof LeanColon) {
                                    std\array_insert($stmt->parent->args, $i, new LeanLineComment('given', $stmt->indent, $stmt->parent));
                                    std\array_insert($declspec, $i, new LeanLineComment('given', $stmt->indent, $stmt->parent));
                                    $modify = true;
                                    ++$i;
                                }
                                $given = $i;
                                break;
                            }
                        }

                        if ($given !== null) {
                            $given = array_slice($declspec, $given);
                            $flattened = [];
                            foreach ($given as $s) {
                                if ($s instanceof LeanArgsSpaceSeparated) {
                                    foreach ($s->args as $a)
                                        $flattened[] = $a;
                                } else
                                    $flattened[] = $s;
                            }
                            $given = $flattened;
                            $latex = [];
                            $givenStart = null;
                            $givenStop = null;
                            $vars = null;
                            foreach (std\enumerate($given) as [$i, $stmt]) {
                                if ($stmt instanceof LeanParenthesis) {
                                    $colon = $stmt->arg;
                                    if ($colon instanceof LeanColon) {
                                        $prop = $colon->rhs;
                                        if (!isset($vars)) {
                                            $vars = $this->parse_vars($implicit);
                                            foreach ($decidables as $p)
                                                $vars[$p] = "Prop";
                                        }
                                        if ($prop->isProp($vars)) {
                                            $latex[] = [$prop->toLatex($syntax), latex_tag("$colon->lhs")];
                                            if ($givenStart === null)
                                                $givenStart = $i;
                                        } elseif ($givenStart !== null) {
                                            $givenStop = $i;
                                            break;
                                        }
                                    } elseif ($colon instanceof LeanAssign) {
                                        $pivot = $i;
                                        break;
                                    }
                                } elseif ($stmt->is_comment())
                                    $latex[] = null;
                                elseif ($stmt instanceof LeanBrace) {
                                    $pivot = $i;
                                    $given[$pivot] = new LeanParenthesis($stmt->arg, $stmt->indent, $stmt->parent);
                                    $given[$pivot]->is_closed = true;
                                    break;
                                } elseif ($stmt instanceof LeanCaret) {
                                } else {
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "given statement must be of LeanParenthesis Type",
                                        'type' => 'linter'
                                    ];
                                }
                            }
                            $given = array_map(fn($stmt) => preg_replace("/^  /m", "", "$stmt"), $given);
                            if ($givenStart !== null) {
                                if ($givenStop !== null) {
                                    $explicit = array_slice($given, 0, $givenStart);
                                    $default = array_slice($given, $givenStop);
                                    $default[count($default) - 1] .= ' :';
                                    $given = array_slice($given, $givenStart, $givenStop);
                                } else {
                                    $explicit = array_slice($given, 0, $givenStart);
                                    $given = array_slice($given, $givenStart);
                                    $latex[count($latex) - 1][1] .= ' :';
                                    $given[count($given) - 1] .= ' :';
                                }
                            } else {
                                $explicit = $given;
                                $explicit[count($explicit) - 1] .= ' :';
                                $given = null;
                            }

                            if ($given) {
                                if (count($given) > count($latex))
                                    $given = [...array_filter($given)];
                                $latex = array_map(fn($stmt) => $stmt ? "$stmt[0]\\tag*{\$$stmt[1]\$}" : null, $latex);
                                $given = array_map(
                                    function ($args) {
                                        $obj = ['lean' => $args[0]];
                                        if ($args[1])
                                            $obj['latex'] = $args[1];
                                        else
                                            $obj['insert'] = true;
                                        return $obj;
                                    },
                                    std\zipped($given, $latex)
                                );
                            }
                        }
                        $proof = $by ? [$by => self::merge_proof($proof->arg, $echo, $syntax)] : self::merge_proof($proof, $echo, $syntax);
                        $implicit = array_map(fn($stmt) => "$stmt", $implicit);
                        $lemma[] = [
                            'comment' => $comment,
                            'accessibility' => "$accessibility",
                            'attribute' => $attribute,
                            'name' => "$name",
                            'instImplicit' => preg_replace("/^  /m", "", implode("\n", $instImplicit)),
                            'implicit' => preg_replace("/^  /m", "", implode("\n", $implicit)),
                            'explicit' => implode("\n", $explicit),
                            'given' => $given,
                            'default' => implode("\n", $default),
                            'imply' => $imply,
                            'proof' => $proof
                        ];
                        $comment = null;
                    } else
                        $error[] = [
                            'code' => "$declspec",
                            'line' => 0,
                            'info' => "declspec of lemma must be of LeanColon Type",
                            'type' => 'linter'
                        ];
                } else
                    $error[] = [
                        'code' => "$stmt",
                        'line' => 0,
                        'info' => "lemma must be of LeanAssign Type",
                        'type' => 'linter'
                    ];
            } elseif ($stmt instanceof Lean_def)
                $preamble[] = "$stmt";
            elseif ($stmt instanceof Lean_open) {
                $stmt = $stmt->arg;
                if ($stmt instanceof LeanArgsSpaceSeparated) {
                    if (count($stmt->args) == 2 && $stmt->args[1] instanceof LeanParenthesis) {
                        $defs = $stmt->args[1]->arg;
                        $open[] = [
                            $stmt->args[0]->__toString() =>
                            $defs instanceof LeanArgsSpaceSeparated ?
                                array_map(fn($arg) => "$arg", $defs->args) :
                                ["$defs->arg"]
                        ];
                    } else
                        $open[] = array_map(fn($arg) => "$arg", $stmt->args);
                } else
                    $open[] = ["$stmt->text"];
            } elseif ($stmt instanceof Lean_set_option) {
                $stmt = $stmt->arg;
                if ($stmt instanceof LeanArgsSpaceSeparated)
                    $set_option[] = array_map(fn($arg) => "$arg", $stmt->args);
            } elseif ($stmt instanceof LeanLineComment) {
                if (preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', "$stmt->text", $matches))
                    $date[$matches[1]] = $matches[2];
                else
                    $comment = "$stmt->text";
            } elseif ($stmt instanceof LeanBlockComment)
                $comment = "$stmt->text";
        }

        return [
            'imports' => $import,
            'open' => $open,
            'set_option' => $set_option,
            'preamble' => $preamble,
            'lemma' => $lemma,
            'date' => $date,
            'meta' => ['error' => $error],
        ];
    }

    static function merge_proof($proof, $echo, &$syntax = null)
    {
        $proof = $proof->args;
        if ($proof[0] instanceof LeanLineComment && $proof[0]->text == 'proof')
            array_shift($proof);

        $proof = array_filter($proof, fn($stmt) => !($stmt instanceof LeanCaret));
        $code = [];
        $last = [];
        $statements = [];
        foreach ($proof as $s)
            array_push($statements, ...$s->split($syntax));

        if ($echo) {
            foreach ($statements as $stmt) {
                if ($echo = $stmt->getEcho()) {
                    $code[] = [$last, is_int($echo->line) ? null : $echo->line];
                    $last = [];
                } else
                    $last[] = $stmt;
            }
        } else {
            foreach ($statements as $stmt) {
                if ($stmt instanceof Lean_let || $stmt instanceof LeanTactic) {
                    $last[] = $stmt;
                    $code[] = [$last, null];
                    $last = [];
                } else
                    $last[] = $stmt;
            }
        }
        if ($last)
            $code[] = [$last, null];
        return array_map(
            fn($code) =>
            [
                'lean' => implode("\n", array_map(fn($stmt) => preg_replace("/^  /m", "", rtrim("$stmt", "\n")), $code[0])),
                'latex' => $code[1]
            ],
            $code
        );
    }

}

abstract class LeanCommand extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
        ];
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

class Lean_import extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'import';

            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_open extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'open';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_set_option extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'set_option';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function echo()
    {
        $arg = &$this->arg;
        if ($arg instanceof LeanArgsSpaceSeparated) {
            $args = &$arg->args;
            if (count($args) == 2 && $args[0] instanceof LeanToken && $args[1] instanceof LeanToken) {
                $value = &$args[1]->text;
                if ($args[0]->text == 'maxHeartbeats')
                    $value = strval(intval($value) * 5);
            }
        }
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_namespace extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'namespace';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBar extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                //must be >= LeanAssign::$input_priority
                return LeanAssign::$input_priority;
            case 'operator':
            case 'command':
                return '|';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->arg->echo();
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

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function is_indented()
    {
        return true;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LeanRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LeanStatements) {
                $arrow->rhs = new LeanCaret($arrow->indent, $arrow->level);
                $stmts->swap_echo_star($syntax, $statements);
            }
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

require_once dirname(__FILE__) . '/lean/arrows.php';

require_once dirname(__FILE__) . '/lean/negation.php';

require_once dirname(__FILE__) . '/lean/match.php';

require_once dirname(__FILE__) . '/lean/ite.php';

require_once dirname(__FILE__) . '/lean/args.php';

require_once dirname(__FILE__) . '/lean/tactic.php';

require_once dirname(__FILE__) . '/lean/decl.php';

class Lean_fun extends LeanUnary
{
    public static $input_priority = 18;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'fun';
            case 'command':
                return '\lambda';
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsNewLineSeparated || $parent instanceof LeanStatements;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => $this->arg->jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        return "$this->command\\ %s";
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

class LeanBigOperator extends LeanArgs
{
    public function __construct($bound, $indent, $level, $parent = null)
    {
        parent::__construct([$bound], $indent, $level, $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'bound':
                // bound variable or quantified variable.
                return $this->args[0];
            case 'scope':
                // body or scope of the quantifier.
                return $this->args[1] ?? null;
            case 'stack_priority':
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'bound':
                $this->args[0] = $val;
                break;
            case 'scope':
                $this->args[1] = $val;
                break;
            default:
                parent::__set($vname, $val);
                return;
        }
        $val->parent = $this;
    }

    /**
     * `∫ x : ℝ in a..b, f x` — the `in` domain modifier attaches to the bound as a sibling:
     * bound becomes `LeanArgsSpaceSeparated [oldBound, LeanIn domain]`.
     */
    public function insert($caret, $func, $type)
    {
        if ($func === 'LeanIn' && $type === 'modifier' && $caret === $this->bound && $this->scope === null) {
            $c = new LeanCaret($this->indent, $caret->level);
            $domain = new LeanIn($c, $this->indent, $caret->level);
            $this->bound = new LeanArgsSpaceSeparated([$caret, $domain], $this->indent, $caret->level);
            return $c;
        }
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->bound) {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->scope = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_if($caret)
    {
        if ($this->scope === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->scope = new LeanIte([$caret], $caret->indent, $caret->level);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->scope) {
            if ($new = $this->push_args_indented($this->indent + 2, $newline_count))
                return $new;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
    public function is_indented()
    {
        return ($parent = $this->parent) instanceof LeanStatements || $parent instanceof LeanIte;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => parent::jsonSerialize()
        ];
    }

    public function latexFormat()
    {
        return "$this->command\\limits_{\\substack{%s}} {%s}";
    }

    public function strFormat()
    {
        if (count($this->args) == 1)
            return "$this->operator %s,";
        return "$this->operator %s, %s";
    }

}


require_once dirname(__FILE__) . '/lean/quantifier.php';

require_once dirname(__FILE__) . '/lean/bigops.php';

function compile($code) {
    return LeanParser::$instance->build($code);
}

class LeanParser extends AbstractParser {
    static $instance = null;
    private $root;
    public $tokens;
    public $start_idx;

    public function __construct() {
    }

    public function __toString() {
        return (string)$this->root;
    }

    public function build($text) {
        $this->init();
        if (!str_ends_with($text, "\n"))
            $text .= "\n";
        $this->tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $text));
        $tokens = &$this->tokens;
        $length = count($tokens);
        $this->start_idx = 0;
        $i = &$this->start_idx;
        for ($i = 0; $i < $length; $i++) {
            $this->parse($tokens[$i], $this);
            if (!$this->caret)
                break;
        }
        return $this->root;
    }
    public function init() {
        $caret = new LeanCaret(0, 0);
        $this->caret = $caret;
        $this->root = new LeanModule([$caret], 0, 0);
    }

}

LeanParser::$instance = new LeanParser();

function escape_specials($token)
{
    return preg_replace_callback(
        '/^(\w+?)_(.+)/',
        function($m) {
            $head = $m[1];
            $tail = preg_replace("/[{}_]/", "\\\\$0", $m[2]);
            return strlen($m[1]) == 1 ? "{$head}_{{$tail}}": "$head\\_$tail";
        },
        $token
    );
}

function latex_tag($tag)
{
    return implode(
        '.',
        array_map(
            fn($tag) => escape_specials($tag),
            explode(".", $tag)
        )
    );
}

function get_lake_path() {
    return std\is_linux() ? "~/.elan/bin/lake": escapeshellcmd(getenv('USERPROFILE') . "\\.elan\\bin\\lake.exe");
}

function get_lean_env()
{
    // add to the file D:\wamp64\bin\apache\apache2.4.54.2\conf\extra\httpd-vhosts.conf
    // SetEnv USERPROFILE "C:\Users\admin" / "C:\Users\Administrator"
    // Configure Git environment variables to trust the directory
    $cwd = getcwd();
    $repository = scandir("$cwd/.lake/packages");
    $repository = array_slice($repository, 2); // Remove . and ..
    $env = [
        'GIT_CONFIG_COUNT' => count($repository),
        // Preserve other important environment variables
        'PATH' => getenv('PATH'),
        // tricks for system profile user on Windows
        // Copy-Item -Path "$HOME\.elan" -Destination "C:\Windows\System32\config\systemprofile\.elan" -Recurse -Force
        'SystemRoot' => getenv('SystemRoot'),
        'HOME' => getenv('HOME')
    ];
    $cwd = str_replace("\\", "/", $cwd);
    foreach ($repository as $index => $directory) {
        $env["GIT_CONFIG_KEY_$index"] = "safe.directory";
        $env["GIT_CONFIG_VALUE_$index"] = "$cwd/.lake/packages/$directory";
    }
    return $env;
}

function transformExpr(string $s0, string $s): string {
    if ($s0 === '_') {
        return $s;
    }
    
    // Check if matches pattern: ^[A-Z][a-zA-Z0-9'!₀-₉]+?S
    if (preg_match('/^[A-Z]$/', $s0)) {
        if (preg_match('/^[a-zA-Z0-9\'!₀-₉]+?S/', $s)) {
            return $s0 . $s;
        }
    }
    
    return '_' . $s0 . $s;
}

function transformPrefix(string $s): string {
    // Pattern 1: EqX, NeX, OrX
    if (preg_match('/^(Eq|Ne|Or)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s2 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s2, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 2: SEqX, HEqX, IffX, AndX
    if (preg_match('/^([SH]Eq)(.)(.*)$/', $s, $matches) || preg_match('/^(Iff|And)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s3 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s3, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 3: LtX, LeX, GtX, GeX (with additional characters)
    if (preg_match('/^(L|G)(t|e)(.)(.*)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $s2 = $matches[3];
        $rest = $matches[4];
        
        // Flip the first character
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        $transformed = transformExpr($s2, $rest);
        return $newS0 . $s1 . $transformed;
    }
    
    // Pattern 3 (short version): Lt, Le, Gt, Ge (no additional characters)
    if (preg_match('/^(L|G)(t|e)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        return $newS0 . $s1;
    }
    
    // If no patterns matched, return original string
    return $s;
}

function is_symm_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne"], true);
}

function is_infix_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne", "lt", "le", "gt", "ge", "in", "ou", "et"], true);
}

function parseInfixSegments(array $list, $section = null): array
{
    if (!$section) {
        $section = $list[0];
        $list = array_slice($list, 1);
    }
    $n = count($list);
    if ($n === 0)
        return [];
    if ($n === 1)
        return [$list];

    $result = [];
    $i = 0;
    while ($i < $n) {
        if ($i + 2 >= $n) {
            // push remaining elements as singletons
            for (; $i < $n; $i++) {
                $result[] = [$list[$i]];
            }
            break;
        }
        $x  = $list[$i];
        $op = $list[$i + 1];
        $y  = $list[$i + 2];
        if (is_infix_operator($op)) {
            $result[] = [$x, $op, $y];
            $i += 3;
        } else {
            $result[] = [$x];
            ++$i;
        }
    }
    return [$section, $result];
}

function Not($token) {
    if (is_string($token)) {
        if (str_starts_with($token, 'Not'))
            return substr($token, 3);
        elseif (str_starts_with($token, 'Eq'))
            return "Ne" . substr($token, 2);
        elseif (str_starts_with($token, 'Ne'))
            return "Eq" . substr($token, 2);
        else
            return "Not" . $token;
    }
    if (count($token) == 1)
        return [Not($token[0])];
    return $token;
}
