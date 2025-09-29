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
    '&' => 'LeanBitAnd',
    '|' => 'LeanBitOr',
    '^' => 'LeanPow',
    '<<' => 'Lean_ll',
    '>>' => 'Lean_gg',
    '||' => 'LeanLogicOr',
    '&&' => 'LeanLogicAnd',
    '∨' => 'Lean_lor',
    '∧' => 'Lean_land',
    '∪' => 'Lean_cup',
    '∩' => 'Lean_cap',
    "\\" => 'Lean_setminus',
    '|>.' => 'LeanMethodChaining',
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
    '≃' => 'Lean_simeq',
    '∣' => 'LeanDvd',
];

preg_match_all("/'(\w+)'/", file_get_contents(dirname(__FILE__) . '/../../static/codemirror/mode/lean/tactics.js'), $tactics);
[, $tactics] = $tactics;

abstract class Lean extends IndentedNode
{
    public function is_comment()
    {
        return false;
    }

    public function tokens_space_separated()
    {
        return [];
    }

    public function is_outsider()
    {
        return false;
    }

    public function getEcho() {}

    public function strArgs()
    {
        return $this->args;
    }

    public function toString()
    {
        $format = $this->strFormat();
        $args = $this->strArgs();
        if ($args)
            return sprintf($format, ...$args);
        return $format;
    }

    public function __toString()
    {
        return ($this->is_indented() ? str_repeat(' ', $this->indent) : '') . $this->toString();
    }

    public function latexFormat()
    {
        return $this->strFormat();
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

    public function toLatex(&$syntax = null)
    {
        $format = $this->latexFormat();
        $args = $this->latexArgs($syntax);
        if ($args)
            return sprintf($format, ...$args);
        return $format;
    }

    public function isProp($vars)
    {
        return false;
    }

    public function echo()
    {
    }

    public function traverse()
    {
        yield $this;
    }

    public function set_line($line)
    {
        $this->line = $line;
        return $line;
    }

    public function insert($caret, $func, $type)
    {
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }

    public function insert_space($caret)
    {
        return $caret;
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function insert_end($caret)
    {
        if ($this->parent)
            return $this->parent->insert_end($this);
    }

    public function append($new, $type)
    {
        if ($this->parent)
            return $this->parent->append($new, $type);
    }

    public function push_accessibility($new, $accessibility)
    {
        if ($this->parent)
            return $this->parent->push_accessibility($new, $accessibility);
    }

    public function __clone()
    {
        $this->parent = null;
    }

    public function push_binary($type)
    {
        if ($parent = $this->parent) {
            if ($type::$input_priority > $parent->stack_priority) {
                $new = new LeanCaret($this->indent);
                $parent->replace($this, new $type($this, $new, $this->indent));
                return $new;
            }
            return $parent->push_binary($type);
        }
    }

    public function push_arithmetic($token)
    {
        global $token2classname;
        return $this->push_binary($token2classname[$token]);
    }
    public function push_or()
    {
        $parent = $this->parent;
        return Lean_lor::$input_priority > $parent->stack_priority ? $this->push_multiple("Lean_lor", new LeanCaret($this->indent)) : $parent->push_or();
    }

    public function push_multiple($Type, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $Type) {
            $parent->push($caret);
        } else
            $parent->replace($this, new $Type([$this, $caret], $parent));

        return $caret;
    }

    public function push_token($word)
    {
        return $this->append(new LeanToken($word, $this->indent), "token");
    }

    public function insert_word($caret, $word)
    {
        return $caret->push_token($word);
    }

    public function insert_comma($caret)
    {
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function insert_semicolon($caret)
    {
        if ($this->parent)
            return $this->parent->insert_semicolon($this);
    }

    public function insert_colon($caret)
    {
        return $caret->push_binary('LeanColon');
    }

    public function insert_assign($caret)
    {
        return $caret->push_binary('LeanAssign');
    }
    public function insert_vconstruct($caret)
    {
        return $caret->push_binary('LeanVConstruct');
    }
    public function insert_construct($caret)
    {
        return $caret->push_binary('LeanConstruct');
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

    public function insert_unary($self, $func)
    {
        $parent = $self->parent;
        if ($self instanceof LeanCaret) {
            $caret = $self;
            $new = new $func($caret, $self->indent);
        } else {
            $caret = new LeanCaret($self->indent);
            $new = new $func($caret, $self->indent);
            $new = new LeanArgsSpaceSeparated([$self, $new], $self->indent);
        }
        $parent->replace($self, $new);
        return $caret;
    }

    public function push_post_unary($func)
    {
        $parent = $this->parent;
        if ($func::$input_priority > $parent->stack_priority) {
            $new = new $func($this, $this->indent);
            $parent->replace($this, $new);
            return $new;
        } else
            return $parent->push_post_unary($func);
    }

    public function push_left($Type, $prev_token)
    {
        switch ($Type) {
            case 'LeanParenthesis':
            case 'LeanBracket':
            case 'LeanBrace':
            case 'LeanAngleBracket':
            case 'LeanFloor':
            case 'LeanCeil':
            case 'LeanNorm':
            case 'LeanDoubleAngleQuotation':
                $indent = $this->indent;
                $caret = new LeanCaret($indent);
                if ($Type == 'LeanBracket') {
                    if ($prev_token == ' ') {
                        # consider the case: a ≡ b [MOD n]
                        $self = $this;
                        $parent = $self->parent;
                        while ($parent) {
                            if ($parent instanceof Lean_equiv || $parent instanceof LeanNotEquiv) {
                                $new = new $Type($caret, $indent);
                                $parent->replace($self, new LeanArgsSpaceSeparated([$self, $new], $indent));
                                return $caret;
                            }
                            $self = $parent;
                            $parent = $parent->parent;
                        }
                    }
                    else if (
                        $this instanceof LeanToken || 
                        $this instanceof LeanProperty || 
                        $this instanceof LeanGetElemBase || 
                        $this instanceof LeanInv || 
                        $this instanceof LeanPairedGroup && $this->is_Expr()
                    ) {
                        # consider the case: (f x)[n], f[m][n]
                        $this->parent->replace($this, new LeanGetElem($this, $caret, $indent));
                        return $caret;
                    }
                }
                $new = new $Type($caret, $indent);
                if ($this->parent instanceof LeanArgsSpaceSeparated)
                    $this->parent->push($new);
                else
                    $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent));
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function insert_left($caret, $func, $prev_token = '')
    {
        return $caret->push_left($func, $prev_token);
    }

    public function push_right($func)
    {
        if ($this->parent)
            return $this->parent->push_right($func);
    }

    public function push_attr($caret)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_minus()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function push_quote($quote)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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
            default:
                parent::__set($vname, $val);
        }
    }

    public function insert_sequential_tactic_combinator($caret, $next_token)
    {
        if ($this->parent)
            return $this->parent->insert_sequential_tactic_combinator($this, $next_token);
    }

    public function relocate_last_comment() {}

    public function split(&$syntax = null)
    {
        return [$this];
    }
    public function regexp()
    {
        return [];
    }

    public function insert_then($caret)
    {
        if ($this->parent)
            return $this->parent->insert_then($this);
    }
    public function insert_else($caret)
    {
        if ($this->parent)
            return $this->parent->insert_else($this);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            $parent instanceof LeanStatements || 
            $parent instanceof LeanITE && ($this === $parent->then || $this === $parent->else);
    }

    public function is_space_separated()
    {
        return false;
    }

    public function insert_line_comment($caret, $comment)
    {
        return $caret->push_line_comment($comment);
    }

    public function case_default($key, ...$kwargs)
    {
        return $this;
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
            case 'theorem':
            case 'lemma':
            case 'set_option':
                return $this->append("Lean_$token", "delspec");
            case 'fun':
            case 'match':
                return $this->append("Lean_$token", "expr");
            case 'have':
            case 'let':
            case 'show':
                return $this->append("Lean_$token", "tactic");
            case 'public':
            case 'private':
            case 'protected':
            case 'noncomputable':
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
                $caret = $this->parent->insert_newline($this, $newline_count, $indent, $tokens[$i + $k]);
                $i += $j - 1;
                return $caret;
            case '.':
                if ($this instanceof LeanCaret && ($this->parent instanceof LeanStatements || $this->parent instanceof LeanSequentialTacticCombinator))
                    return $this->parent->insert_unary($this, 'LeanTacticBlock');
                else
                    return $this->push_binary("LeanProperty");
            case 'is':
                if ($this instanceof LeanCaret && $this->parent instanceof LeanProperty)
                    return $this->parent->insert_word($this, $token);
                else {
                    $Type = "Lean_$token";
                    $not = $i + 2 < $count && std\isspace($tokens[$i + 1]) && strtolower($tokens[$i + 2]) == 'not';
                    if ($not) {
                        $i += 2;
                        $Type .= '_not';
                    }
                    return $this->push_binary($Type);
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
            case '?':
                if ($this instanceof LeanGetElem) {
                    $parent = $this->parent;
                    [$lhs, $rhs] = $this->args;
                    $new = new LeanGetElemQue($lhs, $rhs, $this->indent);
                    $parent->replace($this, $new);
                    return $new;
                }
                else {
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
                } elseif ($i + 2 < $count && $tokens[$i + 1] == ';' && $tokens[$i + 2] == '>') {
                    $i += 2;
                    return $this->parent->insert_sequential_tactic_combinator($this, $tokens[$i + 1]);
                } else
                    return $this->push_binary('Lean_lt');
            case '>':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('Lean_ge');
                } else
                    return $this->push_binary('Lean_gt');
            case '≤':
                return $this->push_binary('Lean_le');
            case '≥':
                return $this->push_binary('Lean_ge');
            case '=':
                if ($tokens[$i + 1] == '>') {
                    ++$i;
                    return $this->push_binary('LeanRightarrow');
                }
                elseif ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('LeanBEq');
                } else
                    return $this->push_binary('LeanEq');
            case '!':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->push_binary('Lean_ne');
                } else
                    return $this->parent->insert_unary($this, 'LeanNot');
            case ',':
                return $this->parent->insert_comma($this);
            case ':':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    return $this->parent->insert_assign($this);
                } elseif ($tokens[$i + 1] == ':') {
                    ++$i;
                    if ($tokens[$i + 1] == 'ᵥ') {
                        ++$i;
                        return $this->parent->insert_vconstruct($this);
                    } else
                        return $this->parent->insert_construct($this);
                } else
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
                    return $this->parent->push_arithmetic('||');
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
                    return $this->parent->push_arithmetic('&&');
                } else
                    return $this->parent->insert_bitand($this);
            case "'":
                while (preg_match("/['\w]/", $tokens[$i + 1]))
                    $token .= $tokens[++$i];
                return $this->push_quote($token);
            case '+':
                if ($this instanceof LeanCaret)
                    return $this->parent->insert_unary($this, 'LeanPlus');
                else {
                    if ($tokens[$i + 1] == '+') {
                        ++$i;
                        $token .= '+';
                    }
                    return $this->push_arithmetic($token);
                }
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
            case '^':
            case '<<':
            case '>>':
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
            case '∣':
                return $this->push_arithmetic($token);
            case '←':
                return $this->parent->insert_unary($this, 'Lean_leftarrow');
            case '∀':
                return $this->append('Lean_forall', 'operator');
            case '∃':
                return $this->append('Lean_exists', 'operator');
            case '∑':
                return $this->append('Lean_sum', 'operator');
            case '∏':
                return $this->append('Lean_prod', 'operator');
            case '⋃':
                return $this->append('Lean_bigcup', 'operator');
            case '⋂':
                return $this->append('Lean_bigcap', 'operator');
            case '¬':
                return $this->parent->insert_unary($this, 'Lean_lnot');
            case '√':
                return $this->parent->insert_unary($this, 'Lean_sqrt');
            case '∛':
                return $this->parent->insert_unary($this, 'LeanCubicRoot');
            case '∜':
                return $this->parent->insert_unary($this, 'LeanQuarticRoot');
            case '↑':
                return $this->parent->insert_unary($this, 'Lean_uparrow');
            case '²':
                return $this->push_post_unary('LeanSquare');
            case '³':
                return $this->push_post_unary('LeanCube');
            case '⁴':
                return $this->push_post_unary('LeanTesseract');
            case '⁻':
                if ($tokens[$i + 1] == '¹') {
                    ++$i;
                    return $this->push_post_unary('LeanInv');
                }
                return $this;
            case 'by':
            case 'calc': # modifiers
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
                else {
                    $token = ucfirst($token);
                    return $this->parent->insert($this, "Lean$token", "modifier");
                }
            case '·':
                if ($this->parent instanceof LeanStatements || $this->parent instanceof LeanSequentialTacticCombinator)
                    return $this->parent->insert_unary($this, 'LeanTacticBlock');
                else
                    //Middle Dot token
                    return $this->parent->insert_word($this, $token);
            case '@':
                if ($this instanceof LeanCaret)
                    return $this->parent->insert_unary($this, 'LeanAttribute');
                else
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
                else
                    return $this->parent->push_right('LeanNorm');
            default:
                $token_orig = $token;
                global $tactics;
                $index = std\binary_search($tactics, $token_orig, "strcmp");
                while (preg_match("/['!?\w]/", $tokens[$i + 1])) {
                    ++$i;
                    $token .= $tokens[$i];
                }
                if ($index < count($tactics) && $tactics[$index] == $token_orig)
                    return $this->parent->insert_tactic($this, $token);
                else
                    return $this->parent->insert_word($this, $token);
        }
    }

    public function push_line_comment($comment)
    {
        return $this->parent->push_line_comment($comment);
    }
}

class LeanCaret extends Lean
{
    public function is_indented()
    {
        return $this->parent instanceof LeanArgsNewLineSeparated;
    }

    public function strFormat()
    {
        return '';
    }

    public function push_line_comment($comment)
    {
        $parent = $this->parent;
        $new = new LeanLineComment($comment, $this->indent);
        $parent->replace($this, $new);
        return $new;
    }

    public function push_block_comment($comment, $docstring)
    {
        $parent = $this->parent;
        $func = $docstring ? 'LeanDocString' : 'LeanBlockComment';
        $parent->replace($this, new $func($comment, $this->indent));
        $parent->push($this);
        return $this;
    }

    public function append($new, $type)
    {
        if (is_string($new)) {
            $this->parent->replace($this, new $new($this, $this->indent));
            return $this;
        } else {
            $this->parent->replace($this, $new);
            return $new;
        }
    }

    public function push_accessibility($new, $accessibility)
    {
        $this->parent->replace($this, new $new($accessibility, $this, $this->indent));
        return $this;
    }

    public function jsonSerialize(): mixed
    {
        return "";
    }

    public function push_left($Type, $prev_token)
    {
        $this->parent->replace($this, new $Type($this, $this->indent));
        return $this;
    }

    public function latexFormat()
    {
        return "";
    }

    public function is_outsider()
    {
        return true;
    }
}

class LeanToken extends Lean
{
    public $text;
    public $cache = null;

    public function __construct($text, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->text = $text;
    }

    public function push_quote($quote)
    {
        $this->text .= $quote;
        return $this;
    }

    public function strFormat()
    {
        return $this->text;
    }

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
        return $text;
    }

    public function starts_with_2_letters()
    {
        return preg_match("/^[a-zA-Z]{2,}/", $this->text);
    }

    public function ends_with_2_letters()
    {
        return preg_match("/[a-zA-Z]{2,}$/", $this->text);
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }

    public function append($new, $type)
    {
        if ($this->parent)
            return $this->parent->insert($this, $new, $type);
    }

    public function jsonSerialize(): mixed
    {
        return $this->text;
    }

    public function is_variable()
    {
        return std\fullmatch('/[a-zA-Z_][a-zA-Z_0-9]*/', $this->text);
    }

    public function lower()
    {
        $this->text = strtolower($this->text);
        return $this;
    }

    public function regexp()
    {
        return ["_"];
    }
    public function tokens_space_separated()
    {
        return [$this];
    }

    public function isProp($vars)
    {
        return ($vars[$this->text] ?? null) == 'Prop';
    }

    public function operand_count() {
        preg_match("/\?*$/", $this->text, $m);
        return strlen($m[0]);
    }
    public function is_parallel_operator() {
        return preg_match("/_\?+$/", $this->text);
    }

    public function tactic_block_info() {
        $map = [];
        $map[0][] = $this;
        $this->cache['size'] = 1;
        return $map;
    }

    public function is_TypeStar() {
        // implicit universe variable
        switch ($this->text) {
            case 'Sort':
            case 'Type':
                return true;
        }
    }
}

LeanToken::$subscript_keys = '/[' . implode('', array_keys(LeanToken::$subscript)) . ']+/u';
LeanToken::$supscript_keys = '/[' . implode('', array_keys(LeanToken::$supscript)) . ']+/u';

class LeanLineComment extends Lean
{
    public $text;

    public function __construct($text, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->text = $text;
    }

    public function is_outsider()
    {
        return preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', $this->text);
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
    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep$this->text";
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
}

class LeanBlockComment extends Lean
{
    public $text;

    public function __construct($text, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->text = $text;
    }

    public function is_indented()
    {
        return true;
    }
    public function sep()
    {
        return '';
    }
    public function strFormat()
    {
        return "/-$this->text-/";
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->text];
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line += substr_count($this->text, "\n");
        return $line;
    }

    public function is_comment()
    {
        return true;
    }
}

class LeanDocString extends LeanBlockComment
{
    public $text;

    public function strFormat()
    {
        return "/--\n$this->text\n-/";
    }

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

    public function __clone()
    {
        parent::__clone();
        $this->args = array_map(fn($arg) => clone $arg, $this->args);
        foreach ($this->args as $arg) {
            $arg->parent = $this;
        }
    }

    public function __construct($args, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line);
        }
        return $line;
    }

    public function traverse()
    {
        yield $this;
        foreach ($this->args as $arg) {
            if ($arg != null)
                yield from $arg->traverse();
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

    public function strip_parenthesis()
    {
        return array_map(fn($arg) => $arg instanceof LeanParenthesis && !($arg->arg instanceof LeanMethodChaining || $arg->arg instanceof Lean_rightarrow) ? $arg->arg : $arg, $this->args);
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret instanceof LeanCaret) {
            $this->replace($caret, new LeanTactic($type, $caret, $this->indent));
            return $caret;
        }
        return $this->insert_word($caret, $type);
    }
}

# Frac|Abs|Norm|Length|Sign|Square|Sqrt|Floor|Ceil|Sin|Cos|Tan|Cot|Arg|Neg|Inv|Cast|Coe|Exp|Log|Val|Card|ToNat|Arccos|Arcsin|Arctan|Arccot|Re|Im|Succ
abstract class LeanUnary extends LeanArgs
{
    public static $input_priority = 47;
    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct([], $indent, $parent);
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

    public function replace($old, $new)
    {
        assert($this->arg === $old, new Exception("assert failed: public function replace(\$old, \$new)"));
        $this->arg = $new;
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg->jsonSerialize();
    }

    public function insert_if($caret)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->arg = new LeanITE($caret, $caret->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

abstract class LeanPairedGroup extends LeanUnary
{
    use Closable;
    public static $input_priority = 60;
    public function is_indented()
    {
        $parent = $this->parent;
        return !($parent instanceof LeanTactic || 
            $parent instanceof LeanArgsCommaSeparated || 
            $parent instanceof LeanAssign || 
            $parent instanceof LeanArgsSpaceSeparated || 
            $parent instanceof LeanRelational || 
            $parent instanceof LeanRightarrow || 
            $parent instanceof LeanUnaryArithmeticPre || 
            $parent instanceof LeanArithmetic || 
            $parent instanceof LeanProperty || 
            $parent instanceof LeanColon || 
            $parent instanceof LeanPairedGroup
        );
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanArgsCommaNewLineSeparated([$caret], $indent);
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        if ($caret instanceof LeanArgsCommaSeparated)
            $this->arg->push($caret);
        else
            $this->arg = new LeanArgsCommaSeparated([$this->arg, $caret], $this->indent);
        return $caret;
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function set_line($line)
    {
        $this->line = $line;
        $arg = $this->arg;
        if ($has_newline = ($arg instanceof LeanArgsCommaNewLineSeparated || $arg instanceof LeanStatements))
            ++$line;
        $line = $arg->set_line($line);
        if ($has_newline)
            ++$line;
        return $line;
    }

    public function push_right($func)
    {
        if (get_class($this) == $func) {
            $this->is_closed = true;
            return $this;
        }
        return $this->parent->push_right($func);
    }

    public function insert($caret, $func, $type)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->arg = new $func($caret, $this->indent);
                return $caret;
            }
            if ($caret instanceof LeanToken) {
                $caret = new LeanCaret($this->indent);
                $this->arg = new LeanArgsSpaceSeparated([$this->arg, new $func($caret, $this->indent)], $this->indent);;
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function argFormat() {
        return '%s';
    }
    public function strFormat()
    {
        $arg = $this->argFormat();
        $operator = $this->operator;
        $format = "$operator[0]$arg";
        if ($this->is_closed)
            $format .= $operator[1];
        return $format;
    }

    public function is_Expr() {
        return true;
    }
}

class LeanParenthesis extends LeanPairedGroup
{
    public function is_indented()
    {
        return ($parent = $this->parent) instanceof LeanArgsNewLineSeparated || $parent instanceof LeanArgsCommaNewLineSeparated;
    }
    public function argFormat() {
        $arg = $this->arg;
        if ($arg instanceof LeanBy && ($stmt = $arg->arg) instanceof LeanStatements && end($stmt->args) instanceof LeanCaret) {
            $indent = str_repeat(' ', $this->indent);
            return "%s$indent";
        }
        else
            return '%s';
    }

    public function latexFormat()
    {
        $arg = $this->arg;
        if ($arg instanceof LeanColon && $arg->lhs instanceof LeanBrace)
            return $arg->lhs->latexFormat();
        return '\left( {%s} \right)';
    }

    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanColon && $arg->lhs instanceof LeanBrace)
            return $arg->lhs->latexArgs($syntax);
        return parent::latexArgs($syntax);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            case 'operator':
                return '()';
            default:
                return parent::__get($vname);
        }
    }

    public function append($new, $type)
    {
        $indent = $this->indent;
        $caret = new LeanCaret($indent);
        if (is_string($new)) {
            $new = new $new($caret, $indent);
            if ($this->parent instanceof LeanArgsSpaceSeparated)
                $this->parent->push($new);
            else
                $this->arg = new LeanArgsSpaceSeparated([$this->arg, $new], $indent);
            return $caret;
        } else {
            $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent));
            return $new;
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret === $this->arg) {
                if ($caret instanceof LeanBy && $this->indent == $indent) {
                    $caret = new LeanCaret($indent);
                    $new = new LeanArgsNewLineSeparated([$this->arg, $caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->arg = $new;
                } else {
                    if ($this->indent == $indent)
                        $indent = $this->indent + 2;
                    $caret = new LeanCaret($indent);
                    $new = new LeanArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->arg = new LeanArgsIndented($this->arg, $new, $this->indent);
                }
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_unary($caret, $func)
    {
        if ($caret === $this->arg) {
            $indent = $this->indent;
            if ($caret instanceof LeanCaret)
                $new = new $func($caret, $indent);
            else {
                $caret = new LeanCaret($indent);
                $new = new LeanArgsSpaceSeparated([$this->arg, new $func($caret, $indent)], $indent);
            }
            $this->arg = $new;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function regexp()
    {
        return $this->arg->regexp();
    }

    public function isProp($vars)
    {
        return $this->arg->isProp($vars);
    }
}

class LeanAngleBracket extends LeanPairedGroup
{
    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LeanArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            case 'operator':
                return ['⟨', '⟩'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\langle {%s} \rangle';
    }

    public function tokens_comma_separated()
    {
        $tokens = [];
        $arg  = $this->arg;
        if ($arg instanceof LeanArgsCommaSeparated)
            $tokens = $arg->tokens_comma_separated();
        else
            $tokens = [$arg];
        return $tokens;
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }
}

class LeanBracket extends LeanPairedGroup
{
    public function is_Expr() {
        return false;
    }

    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LeanArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '[]';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left[ {%s} \right]';
    }

    public function push_right($func)
    {
        if (get_class($this) == $func && ($lt = $this->arg) instanceof Lean_lt && $lt->lhs instanceof LeanToken) {
            $new = new LeanStack($lt, $this->indent);
            $caret = new LeanCaret($this->indent);
            $new->scope = $caret;
            $this->parent->replace($this, $new);
            return $caret;
        }
        return parent::push_right($func);
    }
}

class LeanBrace extends LeanPairedGroup
{
    public function is_Expr() {
        return false;
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return !($parent instanceof LeanQuantifier || $parent instanceof LeanBinaryBoolean || $parent instanceof LeanColon || $parent instanceof LeanSetOperator || $parent instanceof LeanTactic || $parent instanceof LeanAssign);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '{}';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\{ {%s} \right\}';
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LeanCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LeanStatements([$caret], $indent);
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
}

class LeanAbs extends LeanPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return '||';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left| {%s} \right|';
    }
}

class LeanNorm extends LeanPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            case 'operator':
                return ['‖', '‖'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lVert {%s} \right\rVert';
    }
}

class LeanCeil extends LeanPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['⌈', '⌉'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lceil {%s} \right\rceil';
    }
}

class LeanFloor extends LeanPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['⌊', '⌋'];
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\left\lfloor {%s} \right\rfloor';
    }
}

class LeanDoubleAngleQuotation extends LeanPairedGroup
{
    public function is_Expr() {
        return false;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            case 'operator':
                return ['«', '»'];
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return false;
    }
}

abstract class LeanBinary extends LeanArgs
{
    public static $input_priority = 47;

    public function __construct($lhs, $rhs, $indent, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $indent, $parent);
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

    public function jsonSerialize(): mixed
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
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

    public function latexFormat()
    {
        return "{%s} $this->command {%s}";
    }

    public function insert_if($caret)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->rhs = new LeanITE($caret, $caret->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanProperty extends LeanBinary
{
    public static $input_priority = 81; // LeanPow::$input_priority + 1
    public function push_attr($caret)
    {
        return parent::push_attr($caret);
    }

    public function sep()
    {
        return '';
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            ($parent instanceof LeanArgsIndented && $parent->rhs === $this) ||
            ($parent instanceof LeanITE && $parent->else === $this);
    }

    public function strFormat()
    {
        return "%s$this->operator%s";
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
    public function latexFormat()
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LeanToken) {
            $command = $rhs->text;
            switch ($command) {
                case 'exp':
                    return '{\color{RoyalBlue} e} ^ {%s}';
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    return "\\$command {%s}";
                case 'fmod':
                    return '{%s} \textcolor{red}{\%%}';
                case 'card':
                    if (!($this->lhs instanceof LeanToken && $this->parent instanceof LeanArgsSpaceSeparated && $this->parent->args[0] === $this))
                        return '\left|{%s}\right|';
                case 'epsilon':
                    if ($this->lhs instanceof LeanToken && $this->lhs->text == 'Hyperreal')
                        return '0^+';
                case 'omega':
                    if ($this->lhs instanceof LeanToken && $this->lhs->text == 'Hyperreal')
                        return '\infty';
            }
        }
        return "{%s}$this->command{%s}";
    }

    public function latexArgs(&$syntax = null)
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LeanToken) {
            switch ($rhs->text) {
                case 'exp':
                    $exponent = $this->lhs;
                    if ($exponent instanceof LeanParenthesis) {
                        $exponent = $exponent->arg;
                    }
                    return [$exponent->toLatex($syntax)];
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                case 'fmod':
                    return [$this->lhs->toLatex($syntax)];
                case 'card':
                    if (!($this->lhs instanceof LeanToken && $this->parent instanceof LeanArgsSpaceSeparated && $this->parent->args[0] === $this))
                        return [$this->lhs->toLatex($syntax)];
            }
        }
        return parent::latexArgs($syntax);
    }
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

    public function insert_left($caret, $func, $prev_token = '')
    {
        if ($func == 'LeanDoubleAngleQuotation')
            return $caret->push_left($func, $prev_token);
        if ($this->parent)
            return $this->parent->insert_left($this, $func, $prev_token);
    }

    public function insert_word($caret, $word)
    {
        if ($caret instanceof LeanCaret)
            return parent::insert_word($caret, $word);
        if ($this->parent)
            return $this->parent->insert_word($this, $word);
    }

    public function push_token($word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }

    public function regexp()
    {
        $func = ucfirst("$this->rhs");
        $regexp = $this->lhs->regexp();
        $regexp = array_map(fn($expr) => "$func$expr", $regexp);
        $regexp[] = "{$func}_";
        return $regexp;
    }

    public function insert_unary($caret, $func)
    {
        if ($this->parent)
            return $this->parent->insert_unary($this, $func);
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                if (str_starts_with($func, 'Lean_'))
                    $caret = $this->insert_word($caret, substr($func, 5));
            } else if ($type == 'modifier') {
                return $this->parent->insert($this, $func, $type);
            } else {
                $caret = new LeanCaret($this->indent);
                $this->parent->replace(
                    $this,
                    new LeanArgsSpaceSeparated(
                        [
                            $this,
                            new $func($caret, $caret->indent)
                        ],
                        $this->indent
                    )
                );
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->parent instanceof LeanTactic && $indent > $this->indent) {
            $caret = new LeanCaret($indent);
            $newline = new LeanArgsNewLineSeparated([$caret], $indent);
            $caret = $newline->push_newlines($newline_count - 1);
            $this->parent->replace($this, new LeanArgsIndented(
                $this,
                $newline,
                $this->indent
            ));
            return $caret;
        }

        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }
}

class LeanColon extends LeanBinary
{
    public static $input_priority = 19;
    public function sep()
    {
        $rhs = $this->rhs;
        return $rhs instanceof LeanStatements ? "\n" : ($rhs instanceof LeanCaret || $this->parent instanceof LeanGetElem ? '' : ' ');
    }

    public function is_indented()
    {
        return false;
    }
    public function strFormat()
    {
        $sep = $this->sep();
        $first = "%s";
        if (!($this->parent instanceof LeanGetElem))
            $first .= " ";
        return "$first$this->operator$sep%s";
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
                $this->rhs = new LeanStatements([$caret], $indent);
                return $caret;
            }
            if ($caret instanceof LeanStatements && $indent == $this->indent && $this->parent instanceof LeanParenthesis)
                return $caret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
}

class LeanAssign extends LeanBinary
{
    public static $input_priority = 18;

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
    public function is_indented()
    {
        return $this->parent instanceof LeanArgsNewLineSeparated;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

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

    public function relocate_last_comment()
    {
        $rhs = $this->rhs;
        $rhs->relocate_last_comment();
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->rhs) {
                if ($caret instanceof LeanCaret) {
                    $caret->indent = $indent;
                    $this->rhs = new LeanArgsNewLineSeparated([$caret], $indent);
                    $caret = $this->rhs->push_newlines($newline_count - 1);
                } else if ($caret instanceof LeanArgsNewLineSeparated) {
                    if ($this->parent)
                        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
                } else {
                    $caret = new LeanCaret($indent);
                    $new = new LeanArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->rhs = new LeanArgsIndented($this->rhs, $new, $this->indent);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function echo()
    {
        $this->rhs->echo();
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function split(&$syntax = null)
    {
        if (($by = $this->rhs) instanceof LeanBy && ($stmts = $by->arg) instanceof LeanStatements) {
            $self = clone $this;
            $self->rhs->arg = new LeanCaret($by->indent);
            $statements[] = $self;
            foreach ($stmts->args as $stmt)
                array_push($statements, ...$stmt->split($syntax));
            return $statements;
        }
        return [$this];
    }

    public function insert_tactic($caret, $type)
    {
        return $this->insert_word($caret, $type);
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
    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

    public function append($new, $type)
    {
        $indent = $this->indent;
        $caret = new LeanCaret($indent);
        if (is_string($new)) {
            $new = new $new($caret, $indent);
            $this->rhs = new LeanArgsSpaceSeparated([$this->rhs, $new], $indent);
            return $caret;
        } else {
            $this->parent->replace($this, new LeanArgsSpaceSeparated([$this, $new], $indent));
            return $new;
        }
    }

    use LeanProp;

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->rhs === $caret && $caret instanceof LeanCaret && $indent > $this->indent) {
            $caret->indent = $indent;
            $this->rhs = new LeanStatements([$caret], $indent);
            return $caret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
}

abstract class LeanRelational extends LeanBinaryBoolean
{
    public static $input_priority = 50;
    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->strip_parenthesis();
        return [$lhs->toLatex($syntax), $rhs->toLatex($syntax)];
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
}


class Lean_gt extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '>';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_ge extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≥';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_lt extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '<';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_le extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≤';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanEq extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '=';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanBEq extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '=\!\!=';
            case 'operator':
                return '==';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bne extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '!=';
            case 'operator':
                return '!=';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_ne extends LeanRelational
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≠';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_equiv extends LeanRelational
{
    public static $input_priority = 32;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≡';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanNotEquiv extends LeanRelational
{
    public static $input_priority = 32;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\not\equiv';
            case 'operator':
                return '≢';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_simeq extends LeanRelational
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '≃';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanDvd extends LeanRelational
{
    public static $input_priority = 50;  # infix[lr]?:\d+ *" *∣
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '{\color{red}{\ \\mid\ }}';
            case 'operator':
                return '∣';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_in extends LeanBinaryBoolean
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∈';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanParenthesis) {
            $lhs = $lhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class Lean_notin extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∉';
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanParenthesis) {
            $lhs = $lhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class Lean_leftrightarrow extends LeanBinaryBoolean
{
    public static $input_priority = 20;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '↔';
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanArithmetic extends LeanBinary
{
    public static $input_priority = 67;
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }
}


class LeanAdd extends LeanArithmetic
{
    public static $input_priority = 65;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '+';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanSub extends LeanArithmetic
{
    public static $input_priority = 65;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '-';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanMul extends LeanArithmetic
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                [$lhs, $rhs] = $this->args;
                if (
                    $rhs instanceof LeanParenthesis && $rhs->arg instanceof LeanDiv ||
                    $rhs instanceof LeanToken && ctype_digit($rhs->text) ||
                    $rhs instanceof LeanMul && $rhs->command ||
                    $lhs instanceof LeanMul && $lhs->command ||
                    $lhs->is_space_separated() ||
                    $lhs instanceof LeanFDiv ||
                    $rhs instanceof LeanPow
                )
                    return '\cdot';
                if (
                    $lhs instanceof LeanToken && ($rhs->is_space_separated() || $rhs instanceof LeanToken && $rhs->starts_with_2_letters()) ||
                    $lhs instanceof LeanToken && $lhs->ends_with_2_letters() && $rhs instanceof LeanToken ||
                    $lhs instanceof LeanProperty || 
                    $rhs instanceof LeanProperty
                )
                    return '\ ';

                return '';

            case 'operator':
                return '*';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        return "%s $this->command %s";
    }
    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($rhs instanceof LeanParenthesis && $rhs->arg instanceof LeanDiv) {
            $rhs = $rhs->arg;
        } elseif ($rhs instanceof LeanNeg)
            $rhs = new LeanParenthesis($rhs, $this->indent);
        elseif ($lhs instanceof LeanNeg)
            $lhs = new LeanParenthesis($lhs, $this->indent);
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}


class Lean_times extends LeanArithmetic
{
    public static $input_priority = 72;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '×';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanMatMul extends LeanArithmetic
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '@';
            case 'command':
                return '{\color{red}\times}';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bullet extends LeanArithmetic
{
    public static $input_priority = 73;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '•';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_odot extends LeanArithmetic
{
    public static $input_priority = 73;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊙';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_otimes extends LeanArithmetic
{
    public static $input_priority = 32;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊗';
            default:
                return parent::__get($vname);
        }
    }
}


class Lean_oplus extends LeanArithmetic
{
    public static $input_priority = 30;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊕';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanDiv extends LeanArithmetic
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '/';
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        $lhs = $this->lhs;
        if ($lhs instanceof LeanDiv) {
            return '\left. {%s} \right/ {%s}';
        } else {
            return '\frac {%s} {%s}';
        }
    }
    public function latexArgs(&$syntax = null)
    {
        $lhs = $this->lhs;
        $rhs = $this->rhs;
        if ($lhs instanceof LeanDiv) {
        } else {
            if ($lhs instanceof LeanParenthesis)
                $lhs = $lhs->arg;
            if ($rhs instanceof LeanParenthesis)
                $rhs = $rhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class LeanFDiv extends LeanArithmetic
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '/\!\!/';
            case 'operator':
                return '//';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanBitAnd extends LeanArithmetic
{
    public static $input_priority = 68;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\\&';
            case 'operator':
                return '&';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBitOr extends LeanArithmetic
{
    // used in the syntax:
    // rcases lt_trichotomy 0 a with ha | h_0 | ha
    public function is_indented()
    {
        return false;
    }

    public function insert_bar($caret, $prev_token, $next)
    {
        if ($caret instanceof LeanToken) {
            $new = new LeanCaret($this->indent);
            $this->replace($caret, new LeanBitOr($caret, $new, $this->indent));
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '|';
            default:
                return parent::__get($vname);
        }
    }

    public function tokens_bar_separated()
    {
        $tokens = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanBitOr)
                $tokens = [...$tokens, ...$arg->tokens_bar_separated()];
            elseif ($arg instanceof LeanAngleBracket)
                $tokens[] = $arg->tokens_comma_separated();
            else
                $tokens[] = $arg;
        }
        return $tokens;
    }

    public function unique_token($indent)
    {
        $tokens = $this->tokens_bar_separated();
        foreach ($tokens as &$token) {
            if (is_array($token)) {
                $token = array_filter($token, fn($token) => $token->text != 'rfl');
                $token = [...$token];
            }
        }
        if (count(
            array_unique(
                array_map(
                    fn($token) =>
                    $token instanceof LeanToken ?
                        $token->text :
                        implode(',', array_map(fn($token) => $token->text, $token)),
                    $tokens
                )
            )
        ) == 1) {
            $token = $tokens[0];
            if (is_array($token) && count($token) == 1)
                $token = $token[0];
            if (is_array($token))
                $token = new LeanArgsCommaSeparated(array_map(
                    function ($token) use ($indent) {
                        $token = clone $token;
                        $token->indent = $indent;
                    },
                    $token
                ), $indent);
            else {
                $token = clone $token;
                $token->indent = $indent;
            }
            return $token;
        }
    }

    public function latexArgs(&$syntax = null)
    {
        if ($this->parent instanceof LeanQuantifier)
            $syntax['setOf'] = true;
        return parent::latexArgs($syntax);
    }
}


class LeanPow extends LeanArithmetic
{
    public static $input_priority = 80;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '^';
            case 'stack_priority':
                return 79;
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LeanParenthesis) {
            if ($lhs->arg instanceof Lean_sqrt || $lhs->arg instanceof LeanPairedGroup || $lhs->arg instanceof LeanArgsSpaceSeparated && ($lhs->arg->is_Abs() || $lhs->arg->is_Bool()))
                $lhs = $lhs->arg;
        }

        if ($rhs instanceof LeanParenthesis)
            $rhs = $rhs->arg;
        return [$lhs->toLatex($syntax), $rhs->toLatex($syntax)];
    }
}


class Lean_ll extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '<<';
            default:
                return parent::__get($vname);
        }
    }
}


class Lean_gg extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '>>';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanModular extends LeanArithmetic
{
    public static $input_priority = 70;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\\%%';
            case 'operator':
                return '%%';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanConstruct extends LeanArithmetic
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '::';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanVConstruct extends LeanArithmetic
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '::_v';
            case 'operator':
                return '::ᵥ';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanAppend extends LeanArithmetic
{
    public static $input_priority = 65;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '+\!\!+';
            case 'operator':
                return '++';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_sqcup extends LeanArithmetic
{
    public static $input_priority = 68;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊔';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_sqcap extends LeanArithmetic
{
    public static $input_priority = 69;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊓';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_cdotp extends LeanArithmetic
{
    public static $input_priority = 71;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⬝';
            case 'command':
                return '{\color{red}\cdotp}';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_circ extends LeanArithmetic
{
    public static $input_priority = 90;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∘';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_blacktriangleright  extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '▸';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanArgsNewLineSeparated;
    }
}

abstract class LeanUnaryArithmetic extends LeanUnary {}

abstract class LeanUnaryArithmeticPost extends LeanUnaryArithmetic
{
    public static $input_priority = 58;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 60;
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanUnaryArithmeticPre extends LeanUnaryArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 67;
            default:
                return parent::__get($vname);
        }
    }
}

class LeanNeg extends LeanUnaryArithmeticPre
{
    public static $input_priority = 75;
    public function sep()
    {
        if ($this->arg instanceof LeanNeg)
            return ' ';
        return '';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis) {
            if (
                $arg->arg instanceof LeanDiv ||
                $arg->arg instanceof LeanMul && !$arg->arg->command
            )
                $arg = $arg->arg;
        }
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 70;
            case 'operator':
            case 'command':
                return '-';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanPlus extends LeanUnaryArithmeticPre
{
    public function strFormat()
    {
        return "$this->operator%s";
    }
    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '+';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanInv extends LeanUnaryArithmeticPost
{
    public static $input_priority = 71;
    public function strFormat()
    {
        return "%s$this->operator";
    }
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⁻¹';
            case 'command':
                return '^{-1}';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_sqrt extends LeanUnaryArithmeticPre
{
    public static $input_priority = 72;
    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis)
            $arg = $arg->arg;
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 71;
            case 'operator':
                return '√';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanSquare extends LeanUnaryArithmeticPost
{
    public function strFormat()
    {
        return "%s$this->operator";
    }

    public function latexFormat()
    {
        return "{%s}$this->command";
    }
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis) {
            if ($arg->arg instanceof Lean_sqrt || $arg->arg instanceof LeanPairedGroup || $arg->arg instanceof LeanArgsSpaceSeparated && ($arg->arg->is_Abs() || $arg->arg->is_Bool()))
                $arg = $arg->arg;
        }
        $syntax['²'] = true; //³⁴
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '²';
            case 'command':
                return '^2';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanCubicRoot extends LeanUnaryArithmeticPre
{
    public function strFormat()
    {
        return "$this->operator%s";
    }
    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 71;
            case 'operator':
                return '∛';
            case 'command':
                return '\sqrt[3]';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_uparrow extends LeanUnaryArithmeticPre
{
    public static $input_priority = 72;
    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis && $arg->arg instanceof LeanArgsSpaceSeparated && $arg->arg->is_Abs())
            $arg = $arg->arg;
        return [$arg->toLatex($syntax)];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 70;
            case 'operator':
                return '↑';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanUparrow extends LeanUnaryArithmeticPre
{
    public static $input_priority = 72;
    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 71;
            case 'operator':
                return '⇑';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanCube extends LeanUnaryArithmeticPost
{
    public function strFormat()
    {
        return "%s$this->operator";
    }

    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '³';
            case 'command':
                return '^3';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanQuarticRoot extends LeanUnaryArithmeticPre
{
    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 71;
            case 'operator':
                return '∜';
            case 'command':
                return '\sqrt[4]';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanTesseract extends LeanUnaryArithmeticPost
{
    public function strFormat()
    {
        return "%s$this->operator";
    }

    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⁴';
            case 'command':
                return '^4';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanPipeForward extends LeanUnaryArithmeticPost
{
    public function strFormat()
    {
        return "%s $this->operator";
    }

    public function latexFormat()
    {
        return "{%s} $this->command";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '|>';
            case 'command':
                return '\text{ |> }';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanMethodChaining extends LeanBinary
{
    public static $input_priority = 67;
    public function sep()
    {
        return '';
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 59;
            default:
                return parent::__get($vname);
        }
    }

    public function strFormat()
    {
        return '%s |>.%s';
    }
    public function latexFormat()
    {
        return '%s\\ \texttt{|>.}%s';
    }
}

abstract class LeanGetElemBase extends LeanBinary
{
    public static $input_priority = 67;
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

    public function push_right($func)
    {
        if ($func == 'LeanBracket')
            return $this;
        return parent::push_right($func);
    }

    public function insert_comma($caret)
    {
        $new = new LeanCaret($this->indent);
        $this->rhs = new LeanArgsCommaSeparated([$caret, $new], $this->indent);
        return $new;
    }
}

class LeanGetElem extends LeanGetElemBase
{
    public function strFormat()
    {
        return '%s[%s]';
    }
    public function latexFormat()
    {
        return '{%s}_{%s}';
    }
}

class LeanGetElemQue extends LeanGetElemBase
{
    public function strFormat()
    {
        return '%s[%s]?';
    }
    public function latexFormat()
    {
        return '{%s}_{%s?}';
    }
}


class Lean_is extends LeanBinary
{
    public static $input_priority = 62;
    public function sep()
    {
        return ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

    public function latexFormat()
    {
        return "{%s}\\ $this->command\\ {%s}";
    }

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

    public function isProp($vars)
    {
        return true;
    }
}

class L_is_not extends LeanBinary
{
    public static $input_priority = 62;
    public function sep()
    {
        return ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

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

    public function isProp($vars)
    {
        return true;
    }
}

abstract class LeanSetOperator extends LeanBinary {
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }
}

class Lean_setminus extends LeanSetOperator
{
    public static $input_priority = 70;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return "\\";
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_cup extends LeanSetOperator
{
    public static $input_priority = 65;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∪';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_cap extends LeanSetOperator
{
    public static $input_priority = 70;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∩';
            default:
                return parent::__get($vname);
        }
    }
}

abstract class LeanLogic extends LeanBinaryBoolean
{
    public $hanging_indentation;
    public function sep()
    {
        return $this->hanging_indentation ? "\n" . str_repeat(' ', $this->rhs->indent) : ' ';
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }
}


class LeanLogicAnd extends LeanLogic
{
    public static $input_priority = 37;

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 50;
            case 'command':
                return '\&\&';
            case 'operator':
                return '&&';
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof Lean_land) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
}


class LeanLogicOr extends LeanLogic
{
    public static $input_priority = 37;

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 36;
            case 'command':
            case 'operator':
                return '||';
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof Lean_lor) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
}

class Lean_lor extends LeanLogic
{
    public static $input_priority = 30;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 29;
            case 'operator':
                return '∨';
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        return [$this->func => [$lhs, $rhs]];
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->rhs && $caret instanceof LeanCaret) {
            if ($indent >= $this->indent) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $this->hanging_indentation = true;
                $caret->indent = $indent;
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }
}

class Lean_land extends LeanLogic
{
    public static $input_priority = 35;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 34;
            case 'operator':
                return '∧';

            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        return [$this->func => [$lhs, $rhs]];
    }
}


class Lean_subseteq extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊆';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_subset extends LeanBinaryBoolean
{
    public static $input_priority = 50;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊂';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_supseteq extends LeanLogic
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊇';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_supset extends LeanLogic
{
    public static $input_priority = 50;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⊃';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanStatements extends LeanArgs
{
    use LeanMultipleLine;
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        for ($i = 0; $i < $newline_count; ++$i) {
            $caret = new LeanCaret($indent);
            $this->push($caret);
        }
        return $caret;
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanITE($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority;
            default:
                return parent::__get($vname);
        }
    }
    public function is_indented()
    {
        return false;
    }
    public function strFormat()
    {
        $format = implode("\n", array_fill(0, count($this->args), '%s'));
        if ($this->parent instanceof LeanBrace)
            $format = "\n$format\n" . str_repeat(' ', $this->parent->indent);
        return $format;
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

    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof LeanCaret)
            array_pop($args);
        if (count($args) == 1)
            [$args] = $args;
        return $args;
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
                    $last = array_pop($this->args);
                    std\array_insert(
                        $parent->args,
                        std\index($parent->args, $self) + 1,
                        $last
                    );
                    $last->parent = $parent;
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

    public function echo()
    {
        $args = &$this->args;
        for ($index = 0; $index < count($args) - 1; ++$index) {
            $result = $args[$index]->echo();
            if (is_array($result)) {
                // zero-th element is the length to be replaced
                $length = array_shift($result);
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
        } elseif ($tactic instanceof LeanTacticBlock)
            $tactic->echo();
    }

    public function isProp($vars)
    {
        $args = &$this->args;
        if (count($args) == 1)
            return $args[0]->isProp($vars);
    }
}


class LeanModule extends LeanStatements
{
    use LeanMultipleLine;
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
                if ($stmt instanceof Lean_have || $stmt instanceof LeanTactic) {
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

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->push(new $func($caret, $this->indent));
                return $caret;
            }
        }
        return $caret;
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

    public function echo2vue($leanFile)
    {
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
            $imports = implode(' ', array_map(fn($import) => "$import", $imports));
            // $cmd = "$lakePath build $imports";
            $cmd = $lakePath . " setup-file \"$leanEchoFile\" Init $imports";
            error_log("executing cmd = $cmd");
            if (std\is_linux())
                shell_exec($cmd);
            else
                std\exec($cmd, $_, get_lean_env());
        }
        // 10000 heartbeats approximates 1 second
        $cmd = $lakePath . ' env lean -D"linter.unusedTactic=false" -D"linter.dupNamespace=false" -D"diagnostics.threshold=1000" -D"maxHeartbeats=4000000" '. escapeshellarg($leanEchoFile);
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
                if ($err['type'] == 'error' && $err['info'] == "no goals to be solved")
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
        array_push($codes['error'], ...$error);
        return $codes;
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
        $this->relocate_last_comment();
        $import = [];
        $open = [];
        $set_option = [];
        $def = [];
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
                            $implyLatex = "\\begin{align}\n$implyLatex\n\\end{align}";
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
                        if ($declspec instanceof LeanToken) {
                            $name = $declspec;
                            $declspec = [];
                        } else {
                            [$name, $declspec] = $declspec->args;
                            $declspec = $declspec->args;
                        }

                        $instImplicit = [];
                        $implicit = [];
                        $given = null;
                        $explicit = [];
                        $decidables = [];
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
                                    $modify = true;
                                    ++$i;
                                }
                                $given = $i;
                                break;
                            }
                        }

                        if ($given !== null) {
                            $given = array_slice($declspec, $given);
                            $latex = [];
                            $pivot = null;
                            $vars = null;
                            $indicesToDelete = [];
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
                                        if ($prop->isProp($vars))
                                            $latex[] = [$prop->toLatex($syntax), latex_tag("$colon->lhs")];
                                        else {
                                            $pivot = $i;
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
                                    break;
                                } elseif ($stmt instanceof LeanCaret) {
                                    $indicesToDelete[] = $i;
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
                            if ($pivot === null) {
                                $latex[count($latex) - 1][1] .= ' :';
                                $given[count($given) - 1] .= ' :';
                            } else if ($pivot) {
                                $explicit = array_slice($given, $pivot);
                                $explicit[count($explicit) - 1] .= ' :';
                                $given = array_slice($given, 0, $pivot);
                            } else {
                                $explicit = $given;
                                $explicit[count($explicit) - 1] .= ' :';
                                $given = [];
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
                            'given' => $given,
                            'explicit' => implode("\n", $explicit),
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
                $def[] = "$stmt";
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
            }
            elseif ($stmt instanceof Lean_set_option) {
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
            'def' => $def,
            'lemma' => $lemma,
            'date' => $date,
            'error' => $error,
        ];
    }

    public function import($module)
    {
        $this->unshift(new Lean_import(
            array_reduce(
                preg_split('/\./', $module),
                function ($carry, $token) {
                    $token = new LeanToken($token, 0);
                    return $carry ? new LeanProperty($carry, $token, 0) : $token;
                },
            ),
            0
        ));
    }

    public function echo()
    {
        $args = &$this->args;
        $this->import('sympy.printing.echo');
        for ($index = 0; $index < count($args); ++$index)
            $args[$index]->echo();
    }
}

abstract class LeanCommand extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }
    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
        ];
    }
}

class Lean_import extends LeanCommand
{
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

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
            $new = new LeanCaret($this->indent);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class Lean_open extends LeanCommand
{
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

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
            $new = new LeanCaret($this->indent);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class Lean_set_option extends LeanCommand
{
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

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
            $new = new LeanCaret($this->indent);
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
    public function is_indented()
    {
        return true;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

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

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LeanRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LeanStatements) {
                $arrow->rhs = new LeanCaret($arrow->indent);
                foreach ($stmts->args as $stmt)
                    array_push($statements, ...$stmt->split($syntax));
            }

            return $statements;
        }
        return [$this];
    }

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LeanCaret($this->indent);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
}

class LeanRightarrow extends LeanBinary
{
    public static $input_priority = 19; // same as LeanColon::$input_priority;
    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ($this->rhs instanceof LeanCaret ? '' : ' ');
    }

    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        $lhs = "%s";
        if (!($this->lhs instanceof LeanCaret))
            $lhs .= ' ';
        return "$lhs$this->operator$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret === $this->rhs) {
            if ($caret instanceof LeanCaret || $caret instanceof LeanLineComment) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                    $caret->indent = $indent;
                    $this->rhs = new LeanStatements([$caret], $indent);
                    if (!($caret instanceof LeanCaret))
                        ++$newline_count;
                    for ($i = 1; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($indent);
                        $this->rhs->push($caret);
                    }
                    return $caret;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '=>';
            default:
                return parent::__get($vname);
        }
    }

    public function relocate_last_comment()
    {
        $this->rhs->relocate_last_comment();
    }

    public function echo()
    {
        $token = [];
        if (($parent = $this->parent) instanceof LeanBar && ($parent = $parent->parent) instanceof LeanWith && (($parent = $parent->parent) instanceof Lean_match || $parent instanceof LeanTactic && $parent->func == 'induction')) {
            $token[] = new LeanToken('⊢', $this->rhs->indent);
            $subject = $parent->args[0];
            if ($subject instanceof LeanArgsCommaSeparated) {
                foreach ($subject->args as $sujet) {
                    if ($sujet instanceof LeanColon)
                        $token[] = $sujet->lhs;
                }
            } else if ($subject instanceof LeanColon)
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
            if (count($token) > 1)
                $token = new LeanArgsCommaSeparated(
                    array_map(
                        function ($arg) use ($indent) {
                            $arg = clone $arg;
                            $arg->indent = $indent;
                            return $arg;
                        },
                        $token
                    ),
                    $indent
                );
            else
                [$token] = $token;
            $stmt->unshift(new LeanTactic('echo', $token, $indent));
        }
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }
}

class Lean_rightarrow extends LeanBinary
{
    public static $input_priority = 25; // right associative operator
    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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

    public function isProp($vars)
    {
        [$lhs, $rhs] = $this->args;
        return ($lhs instanceof LeanToken && (($vars["$lhs"] ?? 'Prop') == 'Prop') || $lhs->isProp($vars)) &&
            ($rhs instanceof LeanToken && (($vars["$rhs"] ?? 'Prop') == 'Prop') || $rhs->isProp($vars));
    }
}

class Lean_mapsto extends LeanBinary
{
    public function sep()
    {
        return $this->rhs instanceof LeanStatements ? "\n" : ' ';
    }
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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
}

class Lean_leftarrow extends LeanUnary
{
    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '←';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_lnot extends LeanUnary
{
    public static $input_priority = 40;
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    use LeanProp;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '¬';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanNot extends LeanUnary
{
    public static $input_priority = 40;
    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    use LeanProp;

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '!';
            case 'command':
                return '\text{!}';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_match extends LeanArgs
{
    public function __construct($subject, $indent, $parent = null)
    {
        parent::__construct([$subject], $indent, $parent);
    }

    public function insert($caret, $func, $type)
    {
        if (!$this->with && $func == 'LeanWith') {
            $caret = new LeanCaret($this->indent);
            $with = new $func($caret, $this->indent);
            $this->with = $with;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return true;
    }

    public function strFormat()
    {
        if ($this->with)
            return "$this->operator %s %s";
        return "$this->operator %s";
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

    public function insert_comma($caret)
    {
        if ($caret === $this->subject) {
            $caret = new LeanCaret($this->indent);
            $this->subject = new LeanArgsCommaSeparated([$this->subject, $caret], $this->indent);
            return $caret;
        }
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function relocate_last_comment()
    {
        $with = $this->with;
        if ($with instanceof LeanWith)
            $with->relocate_last_comment();
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        return parent::insert_tactic($caret, $token);
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
}

class LeanITE extends LeanArgs
{
    public static $input_priority = 60;
    public function __construct($if, $indent, $parent = null)
    {
        parent::__construct([$if], $indent, $parent);
    }

    public function insert_then($caret)
    {
        if (!$this->then) {
            $caret = new LeanCaret($this->indent + 2);
            $this->then = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function insert_else($caret)
    {
        if (!$this->else) {
            $caret = new LeanCaret($this->indent + 2);
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
                $this->else = new LeanITE($caret, $this->indent);
                return $caret;
            }
            if ($caret === $this->then) {
                $this->then = new LeanITE($caret, $this->indent + 2);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_colon($caret)
    {
        if ($caret === $this->if) {
            $new = new LeanCaret($caret->indent);
            $this->replace($caret, new LeanColon($caret, $new, $caret->indent));
            return $new;
        }
        return $caret->push_binary('LeanColon');
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->then) {
            if ($caret instanceof Lean_let) {
                $stmt = new LeanStatements([$caret], $caret->indent);
                $this->then = $stmt;
                $caret = new LeanCaret($caret->indent);
                $stmt->push($caret);
            }
            return $caret;
        }
        if ($caret === $this->else) {
            if ($caret instanceof LeanCaret)
                return $caret;
            if ($caret instanceof Lean_let) {
                $stmt = new LeanStatements([$caret], $caret->indent);
                $this->else = $stmt;
                $caret = new LeanCaret($caret->indent);
                $stmt->push($caret);
                return $caret;
            }
        }
            
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements || $parent instanceof LeanITE && $this === $parent->then;
    }

    public function strFormat()
    {
        $else = $this->else;
        $indent_else = str_repeat(' ', $this->indent);
        $sep = $else instanceof LeanITE ? ' ' : "\n";
        $then = $this->then == null? '' : '%s';
        $else = $else == null? '' : '%s';
        return "if %s then\n$then\n{$indent_else}else$sep$else";
    }

    public function latexFormat()
    {
        $cases = 0;
        $else = $this;
        while (true) {
            [$if, $then, $else] = $else->strip_parenthesis();
            ++$cases;

            if (!($else instanceof LeanITE))
                break;
        }

        $cases = implode(
            "\\\\",
            array_fill(0, $cases, "%s")
        );
        return "\\begin{cases} $cases \\\\ {%s} & {\\color{blue}\\text{else}} \\end{cases}";
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

            if (!($else instanceof LeanITE))
                break;
        }

        $else = $else->toLatex($syntax);
        return array_merge($cases, [$else]);
    }

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

    public function set_line($line)
    {
        $this->line = $line;
        [$if, $then, $else] = $this->args;
        $line = $if->set_line($line);
        ++$line;
        $line = $then->set_line($line);
        ++$line;
        if (!($else instanceof LeanITE))
            ++$line;
        return $else->set_line($line);
    }
}

class LeanArgsSpaceSeparated extends LeanArgs
{
    public static $input_priority = 75;
    public $cache = null;
    public function is_space_separated()
    {
        return true;
    }

    public function operand_count() {
        return $this->args[0]->operand_count();
    }

    public function construct_prefix_tree() {
        $tokens = $this->tokens_space_separated();
        $tree = std\eval_prefix($tokens, fn($arg) => $arg->operand_count());
        return $tree;
    }

    public function tactic_block_info() {
        if (isset($this->cache['tactic_block_info']))
            return $this->cache['tactic_block_info'];
        $nodes = $this->construct_prefix_tree();
        $physic_index = 0;
        $logic_index = 0;
        foreach ($nodes as $node) {
            $node->traverse(function($node) use (&$logic_index, &$physic_index, &$nodes){
                if ($parent = $node->parent)
                    $args = &$parent->args;
                else 
                    $args = &$nodes;
                $i = std\index($args, $node);
                if ($i) {
                    foreach (std\range($i - 1, -1, -1) as $j) {
                        $size = $args[$j]->size();
                        if ($args[$j]->cache['physic_index'] + $size == $physic_index)
                            $logic_index = max($logic_index, $args[$j]->func->cache['index'] + $size);
                    }
                }
                elseif ($parent && $parent->func->is_parallel_operator())
                    ++$logic_index;
                $node->func->cache['index'] = $logic_index;
                $node->func->cache['size'] = $node->size();
                $node->cache['physic_index'] = $physic_index;
                ++$physic_index;
            });
        }
        $tokens = $this->tokens_space_separated();
        $map = [];
        foreach (array_reverse($tokens) as $token) {
            if ($token->is_parallel_operator())
                --$token->cache['size'];
            $map[$token->cache['index']][] = $token;
        }
        $this->cache['tactic_block_info'] = $map;
        return $map;
    }

    public function tokens_space_separated()
    {
        if (isset($this->cache['tokens_space_separated']))
            return $this->cache['tokens_space_separated'];
        $tokens = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanToken)
                $tokens[] = $arg;
            elseif ($arg instanceof LeanAngleBracket)
                $tokens[] = $arg->tokens_comma_separated();
            else
                return [];
        }
        $this->cache['tokens_space_separated'] = $tokens;
        return $tokens;
    }

    public function unique_token($indent)
    {
        if ($tokens = $this->tokens_space_separated()) {
            if (count(array_unique(array_map(fn($token) => $token->text, $tokens))) == 1) {
                $token = clone $tokens[0];
                $token->indent = $indent;
                return $token;
            }
        }
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements ||
            $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            $parent instanceof LeanITE && ($this === $parent->then || $this === $parent->else);
    }

    public function strFormat()
    {
        return implode(' ', array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        $args = $this->args;
        $func = $args[0];
        if ($this->is_Abs())
            return '\left|{%s}\right|';
        if ($func instanceof LeanToken) {
            switch (count($args)) {
                case 2:
                    switch ($func->text) {
                        case 'exp':
                        case 'cexp':
                            return '{\color{RoyalBlue} e} ^ {%s}';
                        case 'arcsin':
                        case 'arccos':
                        case 'arctan':
                        case 'sin':
                        case 'cos':
                        case 'tan':
                        case 'arg':
                            return "\\$func->text {%s}";
                        case 'arcsec':
                        case 'arccsc':
                        case 'arccot':
                        case 'arcsinh':
                        case 'arccosh':
                        case 'arctanh':
                        case 'arccoth':
                            return "$func->text\\ {%s}";

                        case 'Ici':
                            return '\left[%s, \infty\right)';
                        case 'Iic':
                            return '\left(-\infty, %s\right]';
                        case 'Ioi':
                            return '\left(%s, \infty\right)';
                        case 'Iio':
                            return '\left(-\infty, %s\right)';

                        case 'Zeros':
                            return '\mathbf{0}_{%s}';
                        case 'Ones':
                            return '\mathbf{1}_{%s}';
                    }
                    break;
                case 3:
                    switch ($func->text) {
                        case 'Ioc':
                            return '\left(%s, %s\right]';
                        case 'Ioo':
                            return '\left(%s, %s\right)';
                        case 'Icc':
                            return '\left[%s, %s\right]';
                        case 'Ico':
                            return '\left[%s, %s\right)';
                        case 'KroneckerDelta':
                            return '\delta_{%s %s}';
                    }
                    break;
            }
        } elseif ($this->is_Bool()) {
            return '\left|{%s}\right|';
        } elseif ($func instanceof LeanProperty) {
            if ($func->rhs instanceof LeanToken) {
                switch ($func->rhs->text) {
                    case 'fmod':
                        if (count($args) == 2)
                            return '{%s}{%s}';
                        break;
                }
            }
        }
        return implode("\\ ", array_fill(0, count($args), '{%s}'));
    }

    public function is_Abs()
    {
        $args = $this->args;
        $func = $args[0];
        return $func instanceof LeanToken && count($args) == 2 && $func->text == 'abs';
    }
    public function is_Bool()
    {
        $args = $this->args;
        $func = $args[0];
        return $func instanceof LeanProperty && $func->rhs instanceof LeanToken && $func->rhs->text == 'toNat' && $func->lhs instanceof LeanToken && $func->lhs->text == 'Bool';
    }

    public function latexArgs(&$syntax = null)
    {
        $args = $this->args;
        $func = $args[0];
        if ($this->is_Abs()) {
            $args = $this->strip_parenthesis();
            $arg = $args[1]->toLatex($syntax);
            return [$arg];
        }
        if ($func instanceof LeanToken) {
            $func = $func->text;
            $syntax[$func] = true;
            switch (count($args)) {
                case 2:
                    switch ($func) {
                        case 'exp':
                        case 'cexp':
                            $args = $this->strip_parenthesis();
                            $arg = $args[1]->toLatex($syntax);
                            return [$arg];
                        case 'arcsin':
                        case 'arccos':
                        case 'arctan':
                        case 'sin':
                        case 'cos':
                        case 'tan':
                        case 'arg':
                        case 'arcsec':
                        case 'arccsc':
                        case 'arccot':
                        case 'arcsinh':
                        case 'arccosh':
                        case 'arctanh':
                        case 'arccoth':
                            $arg = $args[1];
                            if ($arg instanceof LeanParenthesis && $arg->arg instanceof LeanDiv)
                                $arg = $arg->arg;
                            $arg = $arg->toLatex($syntax);
                            return [$arg];

                        case 'Ici':
                        case 'Iic':
                        case 'Ioi':
                        case 'Iio':
                        case 'Zeros':
                        case 'Ones':
                            $args = $this->strip_parenthesis();
                            $arg = $args[1]->toLatex($syntax);
                            return [$arg];
                    }
                    break;
                case 3:
                    switch ($func) {
                        case 'Ioc':
                        case 'Ioo':
                        case 'Icc':
                        case 'Ico':
                            $args = $this->strip_parenthesis();
                            $lhs = $args[1]->toLatex($syntax);
                            $rhs = $args[2]->toLatex($syntax);
                            return [$lhs, $rhs];
                        case 'KroneckerDelta':
                            $args = $this->args;
                            $lhs = $args[1]->toLatex($syntax);
                            $rhs = $args[2]->toLatex($syntax);
                            return [$lhs, $rhs];
                    }
                    break;
            }
        } elseif ($this->is_Bool()) {
            $args = $this->strip_parenthesis();
            $arg = $args[1]->toLatex($syntax);
            return [$arg];
        }
        return parent::latexArgs($syntax);
    }

    public function insert_word($caret, $word)
    {
        $new = new LeanToken($word, $this->indent);
        $this->push($new);
        return $new;
    }

    public function insert_unary($caret, $func)
    {
        if ($caret === end($this->args)) {
            $indent = $this->indent;
            if ($caret instanceof LeanCaret) {
                $new = new $func($caret, $indent);
                $this->replace($caret, $new);
            } else {
                $caret = new LeanCaret($indent);
                $new = new $func($caret, $indent);
                $this->push($new);
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function get_type($vars, $arg)
    {
        if ($arg instanceof LeanToken)
            return $vars["$arg"] ?? '';
        if ($arg instanceof LeanArgsSpaceSeparated) {
            $args = array_map(fn($arg) => $this->get_type($vars, $arg), $arg->args);
            return std\getitem($vars, ...$args);
        }
        return '';
    }
    public function isProp($vars)
    {
        $args = array_map(
            fn($arg) => $this->get_type($vars, $arg),
            $this->args
        );
        $type = &$args[0];
        if (is_array($type))
            return std\getitem($type, ...array_slice($args, 1)) == 'Prop';

        $func = $this->args[0];
        if ($func instanceof LeanToken) {
            switch ($func->text) {
                case 'HEq':
                    return true;
            }
        }
    }

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args) && !$caret instanceof LeanCaret && $type != 'modifier') {
            $caret = new LeanCaret($this->indent);
            $this->push(new $func($caret, $caret->indent));
            return $caret;
        } else if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }
}

class LeanArgsNewLineSeparated extends LeanArgs
{
    use LeanMultipleLine;
    public function is_indented()
    {
        return false;
    }
    public function strFormat()
    {
        return implode("\n", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return implode("\n", array_fill(0, count($this->args), '{%s}'));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            $end = end($this->args);
            $caret = new LeanCaret($indent);
            if ($end instanceof LeanToken || $end instanceof LeanProperty) {
                // function call
                $new = new LeanArgsNewLineSeparated([$caret], $indent);
                $caret = $new->push_newlines($newline_count - 1);
                $this->replace($end, new LeanArgsIndented($end, $new, $this->indent));
            }
            else
                $this->push($caret);
            return $caret;
        } elseif ($this->parent instanceof LeanAssign && !($caret instanceof LeanLineComment))
            return parent::insert_newline($caret, $newline_count, $indent, $next);
        else {

            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LeanCaret($indent);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof LeanCalc)
                    return 17;
                return 47;
            default:
                return parent::__get($vname);
        }
    }

    public function relocate_last_comment()
    {
        for ($index = count($this->args) - 1; $index >= 0; --$index) {
            $end = $this->args[$index];
            if ($end instanceof LeanCaret || $end->is_comment()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LeanStatements)
                        break;
                    $self = $parent;
                }
                if ($parent) {
                    $last = array_pop($this->args);
                    std\array_insert(
                        $parent->args,
                        std\index($parent->args, $self) + 1,
                        $last
                    );
                    $last->parent = $parent;
                    return $parent->relocate_last_comment();
                }
            } else
                return $end->relocate_last_comment();
        }
    }

    public function push_newlines($newline_count)
    {
        for ($i = 0; $i < $newline_count; ++$i) {
            $this->push(new LeanCaret($this->indent));
        }
        return end($this->args);
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanITE($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanArgsIndented extends LeanBinary
{
    public function sep()
    {
        return "\n";
    }
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s$sep%s";
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "%s$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            $end = end($this->args);
            if ($end instanceof LeanToken || $end instanceof LeanProperty) {
                // function call
                $caret = new LeanCaret($indent);
                $new = new LeanArgsNewLineSeparated([$caret], $indent);
                $caret = $new->push_newlines($newline_count - 1);
                $this->replace($end, new LeanArgsIndented($end, $new, $this->indent));
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent instanceof LeanAssign)
            return parent::insert_newline($caret, $newline_count, $indent, $next);
        else {

            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LeanCaret($indent);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof LeanCalc)
                    return 17;
                return 47;
            default:
                return parent::__get($vname);
        }
    }

    public function relocate_last_comment()
    {
        for ($index = count($this->args) - 1; $index >= 0; --$index) {
            $end = $this->args[$index];
            if ($end instanceof LeanCaret || $end->is_comment()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LeanStatements)
                        break;
                    $self = $parent;
                }
                if ($parent) {
                    $last = array_pop($this->args);
                    std\array_insert(
                        $parent->args,
                        std\index($parent->args, $self) + 1,
                        $last
                    );
                    $last->parent = $parent;
                    return $parent->relocate_last_comment();
                }
            } else
                return $end->relocate_last_comment();
        }
    }
}

class LeanArgsCommaSeparated extends LeanArgs
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return implode(", ", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return implode(", ", array_fill(0, count($this->args), '{%s}'));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof LeanBar)
                    return LeanColon::$input_priority;
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        $this->push($caret);
        return $caret;
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            } elseif ($this->parent)
                return $this->parent->insert($this, $func, $type);
        }
    }

    public function tokens_comma_separated()
    {
        $tokens = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanToken)
                $tokens[] = $arg;
            elseif ($arg instanceof LeanAngleBracket)
                array_push($tokens, ...$arg->tokens_comma_separated());
        }
        return $tokens;
    }
}

class LeanArgsSemicolonSeparated extends LeanArgs
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return implode("; ", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return implode("; ", array_fill(0, count($this->args), '{%s}'));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_semicolon($caret)
    {
        $caret = new LeanCaret($this->indent);
        $this->push($caret);
        return $caret;
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            } elseif ($this->parent)
                return $this->parent->insert($this, $func, $type);
        }
    }
}

class LeanArgsCommaNewLineSeparated extends LeanArgs
{
    use LeanMultipleLine;
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return implode(",\n", array_fill(0, count($this->args), '%s'));
    }
    public function latexFormat()
    {
        return implode(",\n", array_fill(0, count($this->args), '{%s}'));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count - 1; ++$i) {
                    $caret = new LeanCaret($indent);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        $caret = new LeanCaret($this->indent);
        $this->push($caret);
        return $caret;
    }


    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

abstract class LeanSyntax extends LeanArgs
{
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

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args)) {
            $caret = new LeanCaret($this->indent);
            $this->push(new $func($caret, $this->indent));
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LeanTactic extends LeanSyntax
{
    public $func;
    public $only;

    public function __construct($func, $arg, $indent, $parent = null)
    {
        parent::__construct([$arg], $indent, $parent);
        $this->func = $func;
    }

    public function insert_line_comment($caret, $comment)
    {
        return $this->push_line_comment($comment);
    }

    public function push_line_comment($comment)
    {
        $new = new LeanLineComment($comment, $this->indent);
        $this->push($new);
        return $new;
    }

    public function getEcho()
    {
        if ($this->func == 'echo')
            return $this;
        if ($this->func == 'try' && $this->arg->func == 'echo')
            return $this->arg;
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
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return !$parent || $parent instanceof LeanStatements || $parent instanceof LeanSequentialTacticCombinator && $this->indent >= $parent->indent && !$parent->newline;
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
            else
                $args[] = ' ';
            $args[] = '%s';
        }
        return $func . implode('', $args);
    }

    public function latexFormat()
    {
        $func = escape_specials($this->func);
        if ($this->only)
            $func .= " only";
        //cm-def {color: #00f;} 
        //cm-keyword {color: #708;} 
        //defined in static/codemirror/lib/codemirror.css
        $color = $func == 'sorry'? '770088' : '0000ff';
        $func = "\\textcolor{#$color}{{$func}}";
        if (!($this->arg instanceof LeanCaret))
            $func .= '\ ';
        return $func . implode('\ ', array_fill(0, count($this->args), "%s"));
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
            'only' => $this->only,
            'modifiers' => array_map(fn($modifier) => $modifier->jsonSerialize(), $this->modifiers),
        ];
    }

    public function relocate_last_comment()
    {
        $arg = end($this->args);
        if ($arg instanceof LeanRightarrow || $arg instanceof LeanWith)
            $arg->relocate_last_comment();
    }

    public function insert_only($caret)
    {
        if ($caret === end($this->args)) {
            if ($this->func == 'repeat') {
                $caret = new LeanToken('only', $this->indent);
                $this->arg = new LeanArgsSpaceSeparated(
                    [$this->arg, $caret],
                    $this->indent
                );
            }
            else
                $this->only = true;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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

    public function get_echo_token()
    {
        if ($at = $this->at) {
            $token = $at->arg;
            if ($this->func == 'split') {
                if ($this->has_tactic_block_followed())
                    return;
            }
            else {
                if ($token instanceof LeanArgsSpaceSeparated)
                    $token = new LeanArgsCommaSeparated(
                        array_map(fn($arg) => clone $arg, $token->args),
                        $this->indent
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
                    else if ($arg instanceof LeanArgsSpaceSeparated) {
                        foreach ($arg->tokens_space_separated() as $arg) {
                            if ($arg instanceof LeanToken)
                                $token[] = clone $arg;
                            else if (is_array($arg)) {
                                foreach ($arg as $a)
                                    $token[] = clone $a;
                            }
                        }
                    }
                    else if ($arg instanceof LeanAngleBracket) {
                        $arg = $arg->arg;
                        if ($arg instanceof LeanToken)
                            $token[] = clone $arg;
                        else if ($arg instanceof LeanArgsCommaSeparated)
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
                            else if ($arg->text != 'rfl')
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
                        }
                        else if ($arg instanceof LeanBitOr) {
                            if ($this->has_tactic_block_followed())
                                return;
                            foreach ($arg->tokens_bar_separated() as $arg) {
                                if (is_array($arg))
                                    array_push($token, ...array_filter($arg, fn($t) => $t->text != 'rfl'));
                                else if ($arg->text != 'rfl')
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
            }
            if ($this->has_tactic_block_followed() || $this->parent instanceof LeanSequentialTacticCombinator);
            else if ($⊢)
                $token[] = new LeanToken($⊢, $this->indent);
            switch (count($token)) {
                case 0:
                    break;
                case 1:
                    $token = $token[0];
                    break;
                default:
                    $token = new LeanArgsCommaSeparated(
                        $token,
                        $this->indent
                    );
            }
        }
        return $token;
    }
    public function echo()
    {
        $token = $this->get_echo_token();
        if ($token) {
            if (($by = $this->by) && $by->arg instanceof LeanStatements)
                $by->echo();
            return [
                1,
                $this,
                new LeanTactic('echo', $token, $this->indent)
            ];
        }
        if (($sequential_tactic_combinator = $this->sequential_tactic_combinator) && $sequential_tactic_combinator->arg->indent)
            $sequential_tactic_combinator->echo();
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
                    $statements = $block->arg->args;
                    $block->arg = new LeanCaret(0);
                    $array = [$self];
                    foreach ($statements as $stmt)
                        array_push($array, ...$stmt->split($syntax));
                    return $array;
                }
            }
            elseif ($block instanceof LeanTactic && $block->indent >= $this->indent) {
                $self = clone $this;
                if ($sequential_tactic_combinator->newline) {
                    $block = $self->sequential_tactic_combinator;
                    assert(end($self->args) instanceof LeanSequentialTacticCombinator);
                    array_pop($self->args);
                }
                else {
                    $block = $self->sequential_tactic_combinator->arg;
                    $self->sequential_tactic_combinator->arg = new LeanCaret(0);
                }
                $array = [$self];
                array_push($array, ...$block->split($syntax));
                return $array;
            }
        }
        if (($by = $this->by) && ($stmts = $by->arg) instanceof LeanStatements) {
            $self = clone $this;
            $self->by->arg = new LeanCaret($by->indent);
            $statements[] = $self;
            foreach ($stmts->args as $stmt)
                array_push($statements, ...$stmt->split($syntax));
            return $statements;
        }
        return [$this];
    }

    public function insert_sequential_tactic_combinator($caret, $next_token)
    {
        if ($caret === end($this->args)) {
            if ($caret instanceof LeanCaret)
                $this->replace($caret, new LeanSequentialTacticCombinator($caret, $this->indent, $next_token != "\n"));
            else {
                $caret = new LeanCaret(0); # use 0 as the temporary indentation
                $this->push(new LeanSequentialTacticCombinator($caret, $this->indent));
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret === end($this->args) && $caret instanceof LeanCaret) {
            if ($this->func == 'try') {
                $caret->parent->replace($caret, new LeanTactic($type, $caret, $this->indent));
                return $caret;
            } else
                return $this->insert_word($caret, $type);
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->arg) {
            if ($this->indent < $indent) {
                if ($caret instanceof LeanArgsSpaceSeparated) {
                    $new = new LeanCaret($this->indent);
                    $caret->push($new);
                    return $new;
                }
            }
            if ($next == '<') {
                // possibly newline-indented <;>
                $caret = new LeanCaret($indent);
                $this->push($caret);
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LeanToken || $caret instanceof LeanArithmetic || $caret instanceof LeanPairedGroup) {
                $new = new LeanCaret($this->indent);
                $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent));
                return $new;
            }
            if ($caret instanceof LeanArgsCommaSeparated) {
                $new = new LeanCaret($this->indent);
                $caret->push($new);
                return $new;
            }
        }
        return parent::insert_comma($caret);
    }

    public function insert_semicolon($caret)
    {
        if ($caret === $this->arg) {
            if ($this->func == 'repeat') {
                $new = new LeanCaret($this->indent);
                if ($caret instanceof LeanArgsSemicolonSeparated)
                    $caret->push($new);
                else
                    $this->replace($caret, new LeanArgsSemicolonSeparated([$caret, $new], $this->indent));
                return $new;
            }
        }
        return parent::insert_semicolon($caret);
    }
}

class LeanBy extends LeanUnary
{
    public function is_indented()
    {
        return $this->parent instanceof LeanArgsCommaNewLineSeparated;
    }
    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }
    public function latexFormat()
    {
        //cm-def {color: #00f;} 
        //defined in static/codemirror/lib/codemirror.css
        $arg = $this->arg;
        $command = "\\textcolor{#0000ff}{{$this->command}}";
        if ($arg instanceof LeanStatements)
            return "\\begin{align*}\n$command && \\\\\n%s\n\\end{align*}";
        return "$command\\ %s";
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

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

    public function insert_semicolon($caret)
    {
        if ($caret === $this->arg) {
            $caret = new LeanCaret($this->indent);
            $this->arg = new LeanArgsSemicolonSeparated([$this->arg, $caret], $this->indent);
            return $caret;
        }
        return $this->parent->insert_semicolon($this);
    }
}

class LeanFrom extends LeanUnary
{
    public function is_indented()
    {
        return $this->parent instanceof LeanArgsCommaNewLineSeparated;
    }
    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }
    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanStatements)
            ++$line;
        return $this->arg->set_line($line);
    }

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
}

class LeanCalc extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function sep()
    {
        return $this->arg instanceof LeanArgsNewLineSeparated ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanArgsNewLineSeparated([$caret], $indent);
            return $this->arg->push_newlines($newline_count - 1);
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'calc';
            default:
                return parent::__get($vname);
        }
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LeanArgsNewLineSeparated)
            ++$line;
        return $this->arg->set_line($line);
    }

    public function echo()
    {
        if (($arg = $this->arg) instanceof LeanArgsNewLineSeparated) {
            foreach ($arg->args as $stmt)
                $stmt->echo();
        }
    }
}


class LeanMOD extends LeanUnary
{
    public function is_indented()
    {
        return false;
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

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command\\$sep%s";
    }

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
}


class LeanUsing extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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
}

class LeanAt extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "\\textcolor{#0000ff}{{$this->command}}\ %s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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
}

class LeanIn extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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
}

class LeanGeneralizing extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent <= $indent && $caret instanceof LeanCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LeanStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

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
}

class LeanSequentialTacticCombinator extends LeanUnary
{
    public $newline = null;
    public function __construct($arg, $indent, $newline=false, $parent = null)
    {
        parent::__construct($arg, $indent, $parent);
        $this->newline = $newline;
    }

    public function is_indented()
    {
        return $this->newline;
    }

    public function sep()
    {
        return $this->arg instanceof LeanTacticBlock || $this->arg->indent > 0 && !$this->newline ? "\n" : ' ';
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
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

    public function insert_tactic($caret, $type)
    {
        if ($caret instanceof LeanCaret) {
            $this->arg = new LeanTactic($type, $caret, $caret->indent);
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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

    public function echo()
    {
        if (($arg = $this->arg) instanceof LeanTacticBlock)
            $arg->echo();
        else if ($arg->indent > 0) {
            $indent = $arg->indent;
            $echo = new LeanTactic('echo', new LeanToken('⊢', $indent), $indent);
            if (($by_cases = $this->parent) instanceof LeanTactic && $by_cases->func == 'by_cases' && $by_cases->has_tactic_block_followed()) {
                while (($sequential_tactic_combinator = $arg->sequential_tactic_combinator) && $sequential_tactic_combinator->arg->indent)
                    $arg = $sequential_tactic_combinator;
                $arg->push(new LeanSequentialTacticCombinator($echo, $indent, true));
            }
            else {
                $echo->push(new LeanSequentialTacticCombinator($arg, $indent));
                $this->arg = $echo;
                $arg->echo();
            }
        }
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

    public function getEcho()
    {
        if ($this->newline) {
            $echo = $this->arg;
            if ($echo instanceof LeanTactic && $echo->func == 'echo')
                return $echo;
        }
    }
}

class LeanTacticBlock extends LeanUnary
{
    public function is_indented()
    {
        return true;
    }

    public function sep()
    {
        return $this->arg instanceof LeanStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LeanCaret) {
                if ($this->indent <= $indent) {
                    if ($indent == $this->indent)
                        $indent = $this->indent + 2;
                    $caret->indent = $indent;
                    $this->arg = new LeanStatements([$caret], $indent);
                    for ($i = 1; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($indent);
                        $this->arg->push($caret);
                    }
                    return $caret;
                }
            } elseif ($caret instanceof LeanStatements) {
                $block = $caret;
                if ($indent >= $block->indent) {
                    for ($i = 0; $i < $newline_count; ++$i) {
                        $caret = new LeanCaret($block->indent);
                        $block->push($caret);
                    }
                    return $caret;
                }
            } else if ($this->indent < $indent) {
                $caret = new LeanCaret($indent);
                $this->arg->indent = $indent;
                $this->arg = new LeanStatements([$this->arg, $caret], $indent);
                return $caret;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_line_comment($caret, $comment)
    {
        if ($caret instanceof LeanCaret) {
            $indent = $this->indent + 2;
            $new = new LeanLineComment($comment, $indent);
            $this->arg = new LeanStatements([$new], $indent);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

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
                    $token = new LeanToken('⊢', $statements->indent);
                $statements->unshift(new LeanTactic('echo', $token, $statements->indent));
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
                                if (($with = $stmt->with) instanceof LeanWith && ($tokens = $with->tokens_bar_separated())) {
                                    $token = $tokens[$tacticBlockCount];
                                    $indent = $statements->indent;
                                    if (is_array($token)) {
                                        $token = array_filter($token, fn($token) => $token->text != 'rfl');
                                        $token = [...$token];
                                        $token = array_map(function ($token) use ($indent) {
                                            $token = clone $token;
                                            $token->indent = $indent;
                                            return $token;
                                        }, $token);
                                        if (count($token) == 1)
                                            [$token] = $token;
                                        else
                                            $token = new LeanArgsCommaSeparated($token, $indent);
                                    } else {
                                        $token = clone $token;
                                        $token->indent = $indent;
                                    }
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $indent,
                                    ));
                                }
                                break;
                            case "cases'":
                                if (($with = $stmt->with) instanceof LeanWith && ($tokens = $with->tokens_space_separated())) {
                                    $token = $tokens[$tacticBlockCount];
                                    $token = clone $token;
                                    $token->indent = $statements->indent;
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $statements->indent,
                                    ));
                                }
                                break;
                            case 'obtain':
                                if (($assign = $stmt->arg) instanceof LeanAssign && (($bitOr = $assign->lhs) instanceof LeanBitOr) && ($tokens = $bitOr->tokens_bar_separated())) {
                                    $token = $tokens[$tacticBlockCount];
                                    $token = clone $token;
                                    $token->indent = $statements->indent;
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        $token,
                                        $statements->indent,
                                    ));
                                }
                                break;
                            case 'split_ifs':
                                if (($with = $stmt->with) instanceof LeanWith && count($with->args) == 1 && (($tokens = $with->args[0]) instanceof LeanArgsSpaceSeparated || $tokens instanceof LeanToken)) {
                                    $statements->unshift(new LeanTactic(
                                        'echo',
                                        new LeanToken(
                                            '⊢',
                                            $statements->indent
                                        ),
                                        $statements->indent,
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
                                                    $first->arg = new LeanArgsCommaSeparated([$token, $first->arg], $this->indent);
                                                else
                                                    $first->arg->unshift($token);
                                            }
                                            else
                                                array_unshift($new_list, new LeanTactic(
                                                    'echo',
                                                    $token,
                                                    $this->indent
                                                ));
                                            $last = end($new_list);
                                            if ($last instanceof LeanTactic && $last->func == 'echo') {
                                                if ($last->arg instanceof LeanToken)
                                                    $last->arg = new LeanArgsCommaSeparated([$last->arg, $token], $this->indent);
                                                else
                                                    $last->arg->push($token);
                                            }
                                            else
                                                array_push($new_list, new LeanTactic(
                                                    'echo',
                                                    $token,
                                                    $this->indent
                                                ));
                                            array_splice($args, 0, $stop, $new_list);
                                        }
                                        if ($index) {
                                            $prev = $this->parent->args[$index - 1];
                                            if ($prev instanceof LeanTactic && $prev->func == 'echo') {
                                                $first = array_shift($args);
                                                if ($prev->arg instanceof LeanToken) {
                                                    if ($first->arg instanceof LeanToken)
                                                        $prev->arg = new LeanArgsCommaSeparated([$prev->arg, $first->arg], $this->indent);
                                                    else
                                                        $prev->arg = new LeanArgsCommaSeparated([$prev->arg, ...$first->arg->args], $this->indent);
                                                }
                                                else {
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
                                        $echo = new LeanTactic(
                                            'echo',
                                            $token,
                                            $this->indent
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
                                        $statements->unshift(new LeanTactic(
                                            'echo',
                                            $token,
                                            $statements->indent,
                                        ));
                                    }
                                    break;
                                }
                            default:
                                $token = new LeanToken('⊢', $statements->indent);
                                $sequential_tactic_combinator = $stmt->sequential_tactic_combinator;
                                if ($sequential_tactic_combinator) {
                                    $tactic = $sequential_tactic_combinator->arg;
                                    $tactic_token = $tactic->get_echo_token();
                                    if ($tactic_token) {
                                        if ($tactic_token instanceof LeanArgsCommaSeparated) {
                                            $tactic_token->push($token);
                                            $token = $tactic_token;
                                        } else
                                            $token = new LeanArgsCommaSeparated([$tactic_token, $token], $statements->indent);
                                    }
                                }
                                $statements->unshift(new LeanTactic(
                                    'echo',
                                    $token,
                                    $statements->indent,
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
    public function tactic_block($args, $span) {
        $count = 0;
        for ($j = 0; $count < $span && $j < count($args); ++$j) {
            if ($args[$j] instanceof LeanTacticBlock)
                ++$count;
        }
        return $j;
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
            $statements = $this->arg->args;
            $self = clone $this;
            $self->arg = new LeanCaret($this->indent);
            $array = [$self];
            foreach ($statements as $stmt)
                array_push($array, ...$stmt->split($syntax));
            return $array;
        }
        return [$this];
    }
}


class LeanWith extends LeanArgs
{
    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct([$arg], $indent, $parent);
    }
    public function is_indented()
    {
        return false;
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

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep" . implode("\n", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function relocate_last_comment()
    {
        end($this->args)->relocate_last_comment();
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
                    $caret = new LeanCaret($this->indent);
                    $this->push($caret);
                    return $caret;
                }
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_bar($caret, $prev_token, $next)
    {
        $cases = $this->args;
        if (end($cases) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanBar($caret, $this->indent));
                return $caret;
            } else {
                $new = new LeanCaret($this->indent);
                $this->replace($caret, new LeanBitOr($caret, $new, $this->indent));
                return $new;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        return parent::insert_tactic($caret, $token);
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

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LeanCaret($this->indent);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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

    public function tokens_bar_separated()
    {
        if (count($this->args) == 1 && $this->args[0] instanceof LeanBitOr)
            return $this->args[0]->tokens_bar_separated();
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

    public function tokens_space_separated()
    {
        if (count($this->args) == 1 && $this->args[0] instanceof LeanArgsSpaceSeparated)
            return $this->args[0]->tokens_space_separated();
        return [];
    }
}

class LeanAttribute extends LeanUnary
{
    public function is_indented()
    {
        return false;
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

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        return $caret;
    }

    public function append($new, $type)
    {
        return $this->push_accessibility($new, "public");
    }

    public function push_accessibility($new, $accessibility)
    {
        switch ($new) {
            case 'Lean_theorem':
            case 'Lean_lemma':
            case 'Lean_def':
                $caret = new LeanCaret($this->indent);
                $new = new $new($accessibility, $caret, $this->indent);
                $this->parent->replace($this, $new);
                $new->attribute = $this;
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

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
}

class Lean_def extends LeanArgs
{
    public function __construct($accessibility, $name, $indent = null, $parent = null)
    {
        if ($indent === null) {
            $indent = $name;
            $name = $accessibility;
            $accessibility = 'public';
        }
        parent::__construct([$name], $indent, $parent);
        array_unshift($this->args, null);
        $this->accessibility = $accessibility;
    }
    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        $accessibilityString = $this->accessibility == 'public' ? '' : "$this->accessibility ";
        $def = "$accessibilityString$this->func %s";
        if ($this->attribute)
            $def = "%s\n$def";
        return $def;
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function strArgs()
    {
        [$attribute, $assignment] = $this->args;
        if ($attribute == null)
            return [$assignment];
        return $this->args;
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

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->assignment) {
                if ($caret instanceof LeanToken || $caret instanceof LeanProperty) {
                    $caret = new LeanCaret($indent);
                    $new = new LeanArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->assignment = new LeanArgsIndented(
                        $this->assignment,
                        $new,
                        $this->indent
                    );
                    return $caret;
                }
                if ($caret instanceof LeanColon) {
                    if ($caret->rhs instanceof LeanCaret) {
                        $caret = $caret->rhs;
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LeanStatements([$caret], $indent);
                        return $caret;
                    }
                } elseif ($caret instanceof LeanAssign) {
                    $caret = $this->assignment->rhs;
                    if ($caret instanceof LeanCaret) {
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LeanStatements([$caret], $indent);
                        return $caret;
                    } else
                        return parent::insert_newline($caret, $newline_count, $this->indent, $next);
                }
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
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

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
}

class Lean_theorem extends Lean_def {}

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
                            $statement->push(new LeanTactic(
                                'try',
                                new LeanTactic('echo', $token, $indent),
                                $indent
                            ));
                        }
                        break;
                    }
                }
            }
        }
    }
}

class Lean_let extends LeanUnary
{
    public function is_indented()
    {
        return true;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        //cm-def {color: #00f;} 
        //defined in static/codemirror/lib/codemirror.css
        return "\\textcolor{#0000ff}{{$this->command}}\\ %s";
    }
    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => $this->arg->jsonSerialize()
        ];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            case 'operator':
            case 'command':
                return 'let';
            default:
                return parent::__get($vname);
        }
    }

    public function get_echo_token()
    {
        $assign = $this->arg;
        if ($assign instanceof LeanAssign) {
            $angleBracket = $assign->lhs;
            if ($angleBracket instanceof LeanAngleBracket) {
                $token = $angleBracket->tokens_comma_separated();
                if (count($token) == 1)
                    return $token[0];
                return new LeanArgsCommaSeparated($token, $this->indent);
            }
        }
    }
    public function echo()
    {
        $token = $this->get_echo_token();
        if ($token) {
            $by = $this->arg->rhs;
            if ($by instanceof LeanBy) {
                $stmt = $by->arg;
                if ($stmt instanceof LeanStatements)
                    $stmt->echo();
            }
            return [
                1,
                $this,
                new LeanTactic('echo', $token, $this->indent)
            ];
        }
    }

    public function split(&$syntax = null)
    {
        $assign = $this->arg;
        if ($assign instanceof LeanAssign && ($by = $assign->rhs) instanceof LeanBy && ($stmts = $by->arg) instanceof LeanStatements) {
            $statements = $assign->split($syntax);
            $statements[0] = new static($statements[0], $this->indent);
            return $statements;
        }
        return [$this];
    }
}

class Lean_have extends Lean_let
{
    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }

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
        $assign = $this->arg;
        if ($assign instanceof LeanAssign) {
            $token = $assign->lhs;
            if ($token instanceof LeanColon)
                $token = $token->lhs;
            if ($token instanceof LeanCaret)
                $token = new LeanToken('this', $this->indent);
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
        $assign = $this->arg;
        if ($assign instanceof LeanAssign) {
            $lhs = $assign->lhs;
            if ($lhs instanceof LeanCaret || $lhs instanceof LeanColon && $lhs->lhs instanceof LeanCaret)
                return '';
        }
        return ' ';
    }
}


class Lean_show extends LeanSyntax
{
    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct([$arg], $indent, $parent);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements || $parent instanceof LeanArgsNewLineSeparated;
    }

    public function strFormat()
    {
        return "$this->func " . implode(' ', array_fill(0, count($this->args), "%s"));
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => parent::jsonSerialize()
        ];
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
}

class Lean_fun extends LeanUnary
{
    public static $input_priority = 18;
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanArgsNewLineSeparated || $parent instanceof LeanStatements;
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

    public function latexFormat()
    {
        return "$this->command\\ %s";
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->operator => $this->arg->jsonSerialize()
        ];
    }

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
}

class LbigOperator extends LeanArgs
{
    public function __construct($bound, $indent, $parent = null)
    {
        parent::__construct([$bound], $indent, $parent);
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

    public function is_indented()
    {
        return ($parent = $this->parent) instanceof LeanStatements || ($parent) instanceof LeanITE;
    }

    public function strFormat()
    {
        if (count($this->args) == 1)
            return "$this->operator %s,";
        return "$this->operator %s, %s";
    }

    public function latexFormat()
    {
        return "$this->command\\limits_{\\substack{%s}} {%s}";
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => parent::jsonSerialize()
        ];
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->bound) {
            $caret = new LeanCaret($this->indent);
            $this->scope = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_if($caret)
    {
        if ($this->scope === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->scope = new LeanITE($caret, $caret->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


class LeanQuantifier extends LbigOperator
{
    use LeanProp;
    public static $input_priority = 24;
    public function latexFormat()
    {
        if (count($this->args) == 1)
            return "$this->command\\ {%s},";
        return "$this->command\\ {%s}, {%s}";
    }
}


// universal quantifier
class Lean_forall extends LeanQuantifier
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∀';
            default:
                return parent::__get($vname);
        }
    }
}

// existential quantifier
class Lean_exists extends LeanQuantifier
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∃';
            default:
                return parent::__get($vname);
        }
    }
}


class Lean_sum extends LbigOperator
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∑';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_prod extends LbigOperator
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∏';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bigcap extends LbigOperator
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⋂';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_bigcup extends LbigOperator
{
    public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⋃';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanStack extends LbigOperator
{
    public static $input_priority = 52;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'Stack';
            case 'command':
                return 'Stack';
            case 'stack_priority':
                return 28;
            default:
                return parent::__get($vname);
        }
    }

    public function strFormat()
    {
        return "[%s] %s";
    }

    public function latexFormat()
    {
        return "\left[{%s}\\right]{%s}";
    }

    public function latexArgs(&$syntax = null)
    {
        $syntax[get_class($this)] = true;
        return parent::latexArgs($syntax);
    }
}

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

    public function init() {
        $caret = new LeanCaret(0);
        $this->caret = $caret;
        $this->root = new LeanModule([$caret], 0);
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
