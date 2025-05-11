<?php

require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/../itertools.php';

ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'LAdd',
    '-' => 'LSub',
    '*' => 'LMul',
    '/' => 'LDiv',
    '÷' => 'LEDiv',  // euclidean division
    '//' => 'LFDiv', // floor division
    '%' => 'LMod',
    '×' => 'L_times',
    '•' => 'L_bullet',
    '⬝' => 'L_cdotp',
    '∘' => 'L_circ',
    '▸' => 'L_blacktriangleright',
    '⊙' => 'L_odot',
    '⊕' => 'L_oplus',
    '⊖' => 'L_ominus',
    '⊗' => 'L_otimes',
    '⊘' => 'L_oslash',
    '⊚' => 'L_circledcirc',
    '⊛' => 'L_circledast',
    '⊜' => 'L_circleeq',
    '⊝' => 'L_circleddash',
    '⊞' => 'L_boxplus',
    '⊟' => 'L_boxminus',
    '⊠' => 'L_boxtimes',
    '⊡' => 'L_dotsquare',
    '∈' => 'L_in',
    '∉' => 'L_notin',
    '&' => 'LBitAnd',
    '|' => 'LBitOr',
    '^' => 'LPow',
    '<<' => 'L_ll',
    '>>' => 'L_gg',
    '||' => 'LLogicOr',
    '&&' => 'LLogicAnd',
    '∨' => 'L_lor',
    '∧' => 'L_land',
    '∪' => 'L_cup',
    '∩' => 'L_cap',
    "\\" => 'L_setminus',
    '|>.' => 'LMethodChaining',
    '⊆' => 'L_subseteq',
    '⊇' => 'L_supseteq',
    '⊔' => 'L_sqcup',
    '⊓' => 'L_sqcap',
    '++' => 'LAppend',
];

preg_match_all("/'(\w+)'/", file_get_contents(dirname(__FILE__) . '/../../static/codemirror/mode/lean/tactics.js'), $tactics);
[, $tactics] = $tactics;

abstract class Lean implements JsonSerializable
{

    public $parent = null;
    public $indent;
    public $line;

    public function __construct($indent, $parent = null)
    {
        $this->indent = $indent;
        $this->parent = $parent;
    }

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

    abstract public function strFormat();
    public function toString()
    {
        return sprintf($this->strFormat(), ...$this->strArgs());
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
        return sprintf($this->latexFormat(), ...$this->latexArgs($syntax));
    }

    public function isProp($vars)
    {
        return false;
    }

    public function echo()
    {
        return $this;
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next_token);
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

    public function append_accessibility($new, $accessibility)
    {
        if ($this->parent)
            return $this->parent->append_accessibility($new, $accessibility);
    }

    public function __clone()
    {
        $this->parent = null;
    }

    public function append_binary($type)
    {
        if ($parent = $this->parent) {
            if ($type::$input_priority > $parent->stack_priority) {
                $new = new LCaret($this->indent);
                $parent->replace($this, new $type($this, $new, $this->indent));
                return $new;
            }
            return $parent->append_binary($type);
        }
    }

    public function append_arithmetic($token)
    {
        global $token2classname;
        return $this->append_binary($token2classname[$token]);
    }
    public function append_or()
    {
        $parent = $this->parent;
        return L_lor::$input_priority > $parent->stack_priority ? $this->append_multiple("L_lor", new LCaret($this->indent)) : $parent->append_or();
    }

    public function append_multiple($Type, $caret)
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
        return $this->append(new LToken($word, $this->indent), "token");
    }

    public function insert_token($caret, $word)
    {
        return $caret->push_token($word);
    }

    public function insert_comma($caret)
    {
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function append_semicolon()
    {
        if ($this->parent)
            return $this->parent->append_semicolon();
    }

    public function insert_colon($caret)
    {
        return $caret->append_binary('LColon');
    }

    public function insert_assign($caret)
    {
        return $caret->append_binary('LAssign');
    }
    public function insert_vconstruct($caret)
    {
        return $caret->append_binary('LVConstruct');
    }
    public function insert_construct($caret)
    {
        return $caret->append_binary('LConstruct');
    }
    public function insert_bar($caret, $prev_token, $next_token)
    {
        switch ($next_token) {
            case ' ':
                if ($prev_token == ' ')
                    return $caret->append_arithmetic('|');
                return $this->append_right('LAbs');
            case ')':
                return $this->append_right('LAbs');
            default:
                if (!$next_token)
                    return $this->append_right('LAbs');
                return $this->insert_unary($caret, 'LAbs');
        }
    }

    public function insert_unary($self, $func)
    {
        $parent = $self->parent;
        if ($self instanceof LCaret) {
            $caret = $self;
            $new = new $func($caret, $self->indent);
        } else {
            $caret = new LCaret($self->indent);
            $new = new $func($caret, $self->indent);
            $new = new LArgsSpaceSeparated([$self, $new], $self->indent);
        }
        $parent->replace($self, $new);
        return $caret;
    }

    public function append_post_unary($func)
    {
        $parent = $this->parent;
        if ($func::$input_priority > $parent->stack_priority) {
            $new = new $func($this, $this->indent);
            $parent->replace($this, $new);
            return $new;
        } else
            return $parent->append_post_unary($func);
    }

    public function append_left($Type, $prev_token)
    {
        switch ($Type) {
            case 'LParenthesis':
            case 'LBracket':
            case 'LBrace':
            case 'LAngleBracket':
            case 'LFloor':
            case 'LCeil':
            case 'LNorm':
            case 'LDoubleAngleQuotation':
                $indent = $this->indent;
                $caret = new LCaret($indent);
                $indexed = false;
                if ($Type == 'LBracket') {
                    $self = $this;
                    $parent = $self->parent;
                    while ($parent) {
                        if ($parent instanceof L_equiv || $parent instanceof LNotEquiv) {
                            $new = new $Type($caret, $indent);
                            $parent->replace($self, new LArgsSpaceSeparated([$self, $new], $indent));
                            return $caret;
                        }
                        $self = $parent;
                        $parent = $parent->parent;
                    }
                    if ($this instanceof LToken || $this instanceof LProperty || $this instanceof LParenthesis)
                        $indexed = $prev_token != ' ';
                }

                if ($indexed)
                    $this->parent->replace($this, new LGetElem($this, $caret, $indent));
                else {
                    $new = new $Type($caret, $indent);
                    if ($this->parent instanceof LArgsSpaceSeparated)
                        $this->parent->push($new);
                    else
                        $this->parent->replace($this, new LArgsSpaceSeparated([$this, $new], $indent));
                }
                return $caret;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function insert_left($caret, $func, $prev_token = '')
    {
        return $caret->append_left($func, $prev_token);
    }

    public function append_right($func)
    {
        if ($this->parent)
            return $this->parent->append_right($func);
    }

    public function append_attr($caret)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_minus()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_quote($quote)
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                return $this->parent->root;
            case 'stack_priority':
                return static::$input_priority;
        }
    }

    public function insert_sequential_tactic_combinator($caret)
    {
        if ($this->parent)
            return $this->parent->insert_sequential_tactic_combinator($this);
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
        return $parent instanceof LArgsCommaNewLineSeparated ||
            $parent instanceof LArgsNewLineSeparated ||
            $parent instanceof LITE && ($this === $parent->then || $this === $parent->else);
    }

    public function is_space_separated()
    {
        return false;
    }

    public function insert_line_comment($caret, $comment)
    {
        return $caret->append_line_comment($comment);
    }
}

class LCaret extends Lean
{
    public function is_indented()
    {
        return $this->parent instanceof LArgsNewLineSeparated;
    }
    public function __get($vname)
    {
        switch ($vname) {
            case 'args':
                return [];
            default:
                return parent::__get($vname);
        }
    }

    public function strFormat()
    {
        return '';
    }

    public function append_line_comment($comment)
    {
        $parent = $this->parent;
        $new = new LLineComment($comment, $this->indent);
        $parent->replace($this, $new);
        return $new;
    }

    public function append_block_comment($comment, $docstring)
    {
        $parent = $this->parent;
        $func = $docstring ? 'LDocString' : 'LBlockComment';
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

    public function append_accessibility($new, $accessibility)
    {
        $this->parent->replace($this, new $new($accessibility, $this, $this->indent));
        return $this;
    }

    public function jsonSerialize(): mixed
    {
        return "";
    }

    public function append_left($Type, $prev_token)
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

class LToken extends Lean
{
    public $arg;

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->arg = $arg;
    }

    public function append_quote($quote)
    {
        $this->arg .= $quote;
        return $this;
    }

    public function strFormat()
    {
        return '%s';
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
        return '%s';
    }

    public function latexArgs(&$syntax = null)
    {
        $text = escape_specials($this->arg);
        if ($text == $this->arg) {
            $text = preg_replace_callback(
                LToken::$subscript_keys,
                fn($m) => '_{' . strtr($m[0], LToken::$subscript) . '}',
                $text
            );

            $text = preg_replace_callback(
                LToken::$supscript_keys,
                fn($m) => '^{' . strtr($m[0], LToken::$supscript) . '}',
                $text
            );
            if ($text == '_')
                $text = '\\' . $text;
        }
        return [$text];
    }

    public function starts_with_2_letters()
    {
        return preg_match("/^[a-zA-Z]{2,}/", $this->arg);
    }

    public function ends_with_2_letters()
    {
        return preg_match("/[a-zA-Z]{2,}$/", $this->arg);
    }

    public function push_token($word)
    {
        $new = new LToken($word, $this->indent);
        $this->parent->replace($this, new LArgsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }

    public function append($new, $type)
    {
        if ($this->parent)
            return $this->parent->insert($this, $new, $type);
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg;
    }

    public function is_variable()
    {
        return std\fullmatch('/[a-zA-Z_][a-zA-Z_0-9]*/', $this->arg);
    }

    public function lower()
    {
        $this->arg = strtolower($this->arg);
        return $this;
    }

    public function regexp()
    {
        return ["_"];
    }
    public function __get($vname)
    {
        switch ($vname) {
            case 'args':
                return [$this->arg];
            default:
                return parent::__get($vname);
        }
    }

    public function tokens_space_separated()
    {
        return [$this];
    }

    public function isProp($vars)
    {
        return ($vars[$this->arg] ?? null) == 'Prop';
    }
}

LToken::$subscript_keys = '/[' . implode('', array_keys(LToken::$subscript)) . ']+/u';
LToken::$supscript_keys = '/[' . implode('', array_keys(LToken::$supscript)) . ']+/u';

class LLineComment extends Lean
{
    public $arg;

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->arg = $arg;
    }

    public function is_outsider()
    {
        return preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', $this->arg);
    }

    public function is_indented()
    {
        switch ($this->arg) {
            case 'given':
                if (($parent = $this->parent) instanceof LArgsNewLineSeparated &&
                    ($parent = $parent->parent) instanceof LArgsIndented &&
                    ($parent = $parent->parent) instanceof LColon &&
                    ($parent = $parent->parent) instanceof LAssign &&
                    $parent->parent instanceof L_lemma
                )
                    return false;
                break;

            case 'proof';
                if (($parent = $this->parent) instanceof LStatements) {
                    if ($parent->parent instanceof L_by)
                        $parent = $parent->parent;
                    if (($parent = $parent->parent) instanceof LAssign && $parent->parent instanceof L_lemma)
                        return false;
                } elseif (($parent = $this->parent) instanceof LArgsNewLineSeparated) {
                    if (($parent = $parent->parent) instanceof LAssign && $parent->parent instanceof L_lemma)
                        return false;
                }
            case 'imply':
                if (($parent = $this->parent) instanceof LStatements &&
                    ($parent = $parent->parent) instanceof LColon &&
                    ($parent = $parent->parent) instanceof LAssign &&
                    $parent->parent instanceof L_lemma
                )
                    return false;
                break;
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
        return "$this->operator$sep%s";
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->arg];
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command$sep%s";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '--';
            case 'command':
                return '%';
            case 'args':
                return [$this->arg];
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        return $this->args;
    }

    public function is_comment()
    {
        return true;
    }
}

class LBlockComment extends Lean
{
    public $arg;

    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct($indent, $parent);
        $this->arg = $arg;
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
        return "/-%s-/";
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'args':
                return [$this->arg];
            default:
                return parent::__get($vname);
        }
    }

    public function latexArgs(&$syntax = null)
    {
        return $this->args;
    }

    public function set_line($line)
    {
        $this->line = $line;
        $line += substr_count($this->arg, "\n");
        return $line;
    }

    public function is_comment()
    {
        return true;
    }
}

class LDocString extends LBlockComment
{
    public $arg;

    public function strFormat()
    {
        return "/--\n%s\n-/";
    }

    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => $this->arg];
    }
    public function set_line($line)
    {
        $this->line = $line;
        ++$line;
        $line += substr_count($this->arg, "\n");
        ++$line;
        return $line;
    }
}


trait LMultipleLine
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


abstract class LArgs extends Lean
{
    public static $input_priority = 47;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return "\\$this->func";
            case 'func':
                return preg_replace('/^L_?/', '', get_class($this));
            default:
                return parent::__get($vname);
        }
    }

    public $args;
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

    public function replace($old, $new)
    {
        $i = std\index($this->args, $old);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        if (is_array($new)) {
            array_splice($this->args, $i, 1, $new);
            foreach ($new as $el) {
                if (!$el->parent)
                    $el->parent = $this;
            }
        } else {
            $this->args[$i] = $new;
            if (!$new->parent)
                $new->parent = $this;
        }
    }

    public function removeChild($node)
    {
        $i = std\index($this->args, $node);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        std\array_delete($this->args, $i);

        if (count($this->args) == 1) {
            [$arg] = $this->args;
            $parent = $this->parent;
            $parent->replace($this, $arg);
            $arg->parent = $parent;
        }
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function push($arg)
    {
        $this->args[] = $arg;
        $arg->parent = $this;
    }

    public function unshift($arg)
    {
        array_unshift($this->args, $arg);
        $arg->parent = $this;
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
        return array_map(fn($arg) => $arg instanceof LParenthesis && !($arg->arg instanceof LMethodChaining) ? $arg->arg : $arg, $this->args);
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret instanceof LCaret) {
            $this->replace($caret, new LTactic($type, $caret, $this->indent));
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

abstract class LUnary extends LArgs
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
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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
            if ($caret instanceof LCaret) {
                $this->arg = new LITE($caret, $caret->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


abstract class LPairedGroup extends LUnary
{
    public static $input_priority = 60;
    public function is_indented()
    {
        $parent = $this->parent;
        if ($parent instanceof LTactic || $parent instanceof LArgsCommaSeparated || $parent instanceof LAssign || $parent instanceof LArgsSpaceSeparated || $parent instanceof LRelational || $parent instanceof LRightarrow || $parent instanceof LUnaryArithmeticPre || $parent instanceof LArithmetic || $parent instanceof LProperty || $parent instanceof LColon)
            return false;
        return true;
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent) {
            if ($caret instanceof LCaret) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $caret->indent = $indent;
                $this->arg = new LArgsCommaNewLineSeparated([$caret], $indent);
                return $caret;
            } else {
                if ($indent == $this->indent)
                    return $caret;
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
            }
        } else
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function insert_comma($caret)
    {
        $caret = new LCaret($this->indent);
        if ($caret instanceof LArgsCommaSeparated)
            $this->arg->push($caret);
        else
            $this->arg = new LArgsCommaSeparated([$this->arg, $caret], $this->indent);
        return $caret;
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LCaret)
            return $this->insert_token($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($has_newline = $this->arg instanceof LArgsCommaNewLineSeparated)
            ++$line;
        $line = $this->arg->set_line($line);
        if ($has_newline)
            ++$line;
        return $line;
    }

    public function append_right($func)
    {
        if (get_class($this) == $func) {
            if (($lt = $this->arg) instanceof L_lt && $lt->lhs instanceof LToken) {
                $new = new LLamda($lt, $this->indent);
                $caret = new LCaret($this->indent);
                $new->scope = $caret;
                $this->parent->replace($this, $new);
                return $caret;
            }
            return $this;
        }
        return $this->parent->append_right($func);
    }

    public function insert($caret, $func, $type)
    {
        if ($this->arg === $caret) {
            if ($caret instanceof LCaret) {
                $this->arg = new $func($caret, $this->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LParenthesis extends LPairedGroup
{
    public function is_indented()
    {
        return ($parent = $this->parent) instanceof LArgsNewLineSeparated || $parent instanceof LArgsCommaNewLineSeparated;
    }

    public function strFormat()
    {
        $arg = $this->arg;
        if ($arg instanceof L_by && ($stmt = $arg->arg) instanceof LStatements && ($end = end($stmt->args)) instanceof LCaret) {
            $indent = str_repeat(' ', $this->indent);
            return "(%s$indent)";
        }
        return "(%s)";
    }
    public function latexFormat()
    {
        $arg = $this->arg;
        if ($arg instanceof LColon && $arg->lhs instanceof LBrace)
            return $arg->lhs->latexFormat();
        return '\left( {%s} \right)';
    }

    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LColon && $arg->lhs instanceof LBrace)
            return $arg->lhs->latexArgs($syntax);
        return parent::latexArgs($syntax);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            default:
                return parent::__get($vname);
        }
    }

    public function append($new, $type)
    {
        $indent = $this->indent;
        $caret = new LCaret($indent);
        if (is_string($new)) {
            $new = new $new($caret, $indent);
            if ($this->parent instanceof LArgsSpaceSeparated)
                $this->parent->push($new);
            else
                $this->arg = new LArgsSpaceSeparated([$this->arg, $new], $indent);
            return $caret;
        } else {
            $this->parent->replace($this, new LArgsSpaceSeparated([$this, $new], $indent));
            return $new;
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent) {
            if ($caret === $this->arg) {
                if ($caret instanceof L_by && $this->indent == $indent) {
                    $caret = new LCaret($indent);
                    $new = new LArgsNewLineSeparated([$this->arg, $caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->arg = $new;
                } else {
                    if ($this->indent == $indent)
                        $indent = $this->indent + 2;
                    $caret = new LCaret($indent);
                    $new = new LArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->arg = new LArgsIndented($this->arg, $new, $this->indent);
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
            if ($caret instanceof LCaret)
                $new = new $func($caret, $indent);
            else {
                $caret = new LCaret($indent);
                $new = new LArgsSpaceSeparated([$this->arg, new $func($caret, $indent)], $indent);
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


class LAngleBracket extends LPairedGroup
{
    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 10;
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return '⟨%s⟩';
    }
    public function latexFormat()
    {
        return '\langle {%s} \rangle';
    }

    public function tokens_comma_separated()
    {
        $tokens = [];
        $arg  = $this->arg;
        if ($arg instanceof LArgsCommaSeparated)
            $tokens = $arg->tokens_comma_separated();
        else
            $tokens = [$arg];
        return $tokens;
    }
}

class LBracket extends LPairedGroup
{
    public function strArgs()
    {
        $arg = $this->arg;
        if ($arg instanceof LArgsCommaNewLineSeparated)
            $arg = "\n$arg\n" . str_repeat(' ', $this->indent);
        return [$arg];
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
    public function strFormat()
    {
        return '[%s]';
    }
    public function latexFormat()
    {
        return '\left[ {%s} \right]';
    }
}


class LBrace extends LPairedGroup
{
    public function is_indented()
    {
        $parent = $this->parent;
        return !($parent instanceof LQuantifier || $parent instanceof LBinaryBoolean || $parent instanceof LColon);
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
    public function strFormat()
    {
        return '{%s}';
    }
    public function latexFormat()
    {
        return '\left\{ {%s} \right\}';
    }
}


class LAbs extends LPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return '|%s|';
    }
    public function latexFormat()
    {
        return '\left| {%s} \right|';
    }
}

class LNorm extends LPairedGroup
{
    // public static $input_priority = 60;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return '‖%s‖';
    }
    public function latexFormat()
    {
        return '\left\lVert {%s} \right\rVert';
    }
}

class LCeil extends LPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return '⌈%s⌉';
    }
    public function latexFormat()
    {
        return '\left\lceil {%s} \right\rceil';
    }
}

class LFloor extends LPairedGroup
{
    public static $input_priority = 72;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
            default:
                return parent::__get($vname);
        }
    }
    public function strFormat()
    {
        return '⌊%s⌋';
    }
    public function latexFormat()
    {
        return '\left\lfloor {%s} \right\rfloor';
    }
}

class LDoubleAngleQuotation extends LPairedGroup
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 22;
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
        return '«%s»';
    }
}

abstract class LBinary extends LArgs
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
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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
            if ($caret instanceof LCaret) {
                $this->rhs = new LITE($caret, $caret->indent);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LProperty extends LBinary
{
    public static $input_priority = 81; // LPow::$input_priority + 1
    public function append_attr($caret)
    {
        return parent::append_attr($caret);
    }

    public function sep()
    {
        return '';
    }
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LArgsCommaNewLineSeparated ||
            $parent instanceof LArgsNewLineSeparated ||
            ($parent instanceof LArgsIndented && $parent->rhs === $this) ||
            ($parent instanceof LITE && $parent->else === $this);
    }

    public function strFormat()
    {
        return "%s$this->operator%s";
    }

    public function is_space_separated()
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LToken) {
            $command = $rhs->arg;
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
        if ($rhs instanceof LToken) {
            $command = $rhs->arg;
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
                    return '\left|{%s}\right|';
            }
        }
        return "{%s}$this->command{%s}";
    }

    public function latexArgs(&$syntax = null)
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LToken) {
            switch ($rhs->arg) {
                case 'exp':
                    $exponent = $this->lhs;
                    if ($exponent instanceof LParenthesis) {
                        $exponent = $exponent->arg;
                    }
                    return [$exponent->toLatex($syntax)];
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                case 'fmod':
                case 'card':
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
        if ($func == 'LDoubleAngleQuotation')
            return $caret->append_left($func, $prev_token);
        if ($this->parent)
            return $this->parent->insert_left($this, $func, $prev_token);
    }

    public function insert_token($caret, $word)
    {
        if ($caret instanceof LCaret)
            return parent::insert_token($caret, $word);
        if ($this->parent)
            return $this->parent->insert_token($this, $word);
    }

    public function push_token($word)
    {
        $new = new LToken($word, $this->indent);
        $this->parent->replace($this, new LArgsSpaceSeparated([$this, $new], $this->indent));
        return $new;
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_token($caret, $token);
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
            if ($caret instanceof LCaret) {
                if (str_starts_with($func, 'L_'))
                    $caret = $this->insert_token($caret, substr($func, 2));
            } else if ($type == 'modifier') {
                return $this->parent->insert($this, $func, $type);
            } else {
                $caret = new LCaret($this->indent);
                $this->parent->replace(
                    $this,
                    new LArgsSpaceSeparated(
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->parent instanceof LTactic && $indent > $this->indent) {
            $caret = new LCaret($indent);
            $newline = new LArgsNewLineSeparated([$caret], $indent);
            $caret = $newline->push_newlines($newline_count - 1);
            $this->parent->replace($this, new LArgsIndented(
                $this,
                $newline,
                $this->indent
            ));
            return $caret;
        }

        return $this->parent->insert_newline($this, $newline_count, $indent, $next_token);
    }
}

class LColon extends LBinary
{
    public static $input_priority = 20;
    public function sep()
    {
        return $this->rhs instanceof LStatements ? "\n" : ' ';
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

    public function strArgs()
    {
        [$lhs, $rhs] = $this->args;
        if ($lhs instanceof LArgsNewLineSeparated) {
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LCaret && $indent > $this->indent) {
                $caret->indent = $indent;
                $this->rhs = new LStatements([$caret], $indent);
                return $caret;
            }
            if ($caret instanceof LStatements && $indent == $this->indent && $this->parent instanceof LParenthesis)
                return $caret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }
}

class LAssign extends LBinary
{
    public static $input_priority = 19;

    public function sep()
    {
        $rhs = $this->rhs;
        if ($rhs instanceof LArgsNewLineSeparated) {
            $lines = $rhs->args;
            if (count($lines) > 2 || !($lines[1] ?? null instanceof LArgsNewLineSeparated) || $lines[0] ?? null instanceof LLineComment)
                return "\n";
        }
        return ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LArgsNewLineSeparated;
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->rhs) {
                if ($caret instanceof LCaret) {
                    $caret->indent = $indent;
                    $this->rhs = new LArgsNewLineSeparated([$caret], $indent);
                    $caret = $this->rhs->push_newlines($newline_count - 1);
                } else if ($caret instanceof LArgsNewLineSeparated) {
                    if ($this->parent)
                        return $this->parent->insert_newline($this, $newline_count, $indent, $next_token);
                } else {
                    $caret = new LCaret($indent);
                    $new = new LArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->rhs = new LArgsIndented($this->rhs, $new, $this->indent);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next_token);
    }

    public function echo()
    {
        $this->rhs = $this->rhs->echo();
        return $this;
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

trait LProp
{
    public function isProp($vars)
    {
        return true;
    }
}

abstract class LBinaryBoolean extends LBinary
{
    public function sep()
    {
        return $this->rhs instanceof LStatements ? "\n" : ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

    public function append($new, $type)
    {
        $indent = $this->indent;
        $caret = new LCaret($indent);
        if (is_string($new)) {
            $new = new $new($caret, $indent);
            $this->rhs = new LArgsSpaceSeparated([$this->rhs, $new], $indent);
            return $caret;
        } else {
            $this->parent->replace($this, new LArgsSpaceSeparated([$this, $new], $indent));
            return $new;
        }
    }

    use LProp;

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->rhs === $caret && $caret instanceof LCaret && $indent > $this->indent) {
            $caret->indent = $indent;
            $this->rhs = new LStatements([$caret], $indent);
            return $caret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }
}

abstract class LRelational extends LBinaryBoolean
{
    public static $input_priority = 51;
    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->strip_parenthesis();
        return [$lhs->toLatex($syntax), $rhs->toLatex($syntax)];
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_token($caret, $token);
    }
}


class L_gt extends LRelational
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

class L_ge extends LRelational
{
    // public static $input_priority = 51;
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

class L_lt extends LRelational
{
    // public static $input_priority = 51;
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

class L_le extends LRelational
{
    // public static $input_priority = 51;
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

class LEq extends LRelational
{
    // public static $input_priority = 51;
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

class L_ne extends LRelational
{
    // public static $input_priority = 51;
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

class L_equiv extends LRelational
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

class LNotEquiv extends LRelational
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


class L_in extends LBinaryBoolean
{
    public static $input_priority = 51;
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
        if ($lhs instanceof LParenthesis) {
            $lhs = $lhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class L_notin extends LBinaryBoolean
{
    public static $input_priority = 51;

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
        if ($lhs instanceof LParenthesis) {
            $lhs = $lhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class L_leftrightarrow extends LBinaryBoolean
{
    public static $input_priority = 21;

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

abstract class LArithmetic extends LBinary
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


class LAdd extends LArithmetic
{
    public static $input_priority = 66;
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

class LSub extends LArithmetic
{
    public static $input_priority = 66;

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


class LMul extends LArithmetic
{
    public static $input_priority = 71;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                [$lhs, $rhs] = $this->args;
                if (
                    $rhs instanceof LParenthesis && $rhs->arg instanceof LDiv ||
                    $rhs instanceof LToken && ctype_digit($rhs->arg) ||
                    $rhs instanceof LMul && $rhs->command ||
                    $lhs instanceof LMul && $lhs->command ||
                    $lhs->is_space_separated() ||
                    $lhs instanceof LFDiv ||
                    $rhs instanceof LPow
                )
                    return '\cdot';
                if (
                    $lhs instanceof LToken && ($rhs->is_space_separated() || $rhs instanceof LToken && $rhs->starts_with_2_letters()) ||
                    $lhs instanceof LToken && $lhs->ends_with_2_letters() && $rhs instanceof LToken ||
                    $lhs instanceof LProperty || 
                    $rhs instanceof LProperty
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
        if ($rhs instanceof LParenthesis && $rhs->arg instanceof LDiv) {
            $rhs = $rhs->arg;
        } elseif ($rhs instanceof LNeg)
            $rhs = new LParenthesis($rhs, $this->indent);
        elseif ($lhs instanceof LNeg)
            $lhs = new LParenthesis($lhs, $this->indent);
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}


class L_times extends LArithmetic
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

class L_bullet extends LArithmetic
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

class L_odot extends LArithmetic
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

class L_otimes extends LArithmetic
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


class L_oplus extends LArithmetic
{
    public static $input_priority = 31;

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

class LDiv extends LArithmetic
{
    public static $input_priority = 71;

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
        if ($lhs instanceof LDiv) {
            return '\left. {%s} \right/ {%s}';
        } else {
            return '\frac {%s} {%s}';
        }
    }
    public function latexArgs(&$syntax = null)
    {
        $lhs = $this->lhs;
        $rhs = $this->rhs;
        if ($lhs instanceof LDiv) {
        } else {
            if ($lhs instanceof LParenthesis)
                $lhs = $lhs->arg;
            if ($rhs instanceof LParenthesis)
                $rhs = $rhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
}

class LFDiv extends LArithmetic
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

class LBitAnd extends LArithmetic
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


class LBitOr extends LArithmetic
{
    // used in the syntax:
    // rcases lt_trichotomy 0 a with ha | h_0 | ha
    public function is_indented()
    {
        return false;
    }

    public function insert_bar($caret, $prev_token, $next_token)
    {
        if ($caret instanceof LToken) {
            $new = new LCaret($this->indent);
            $this->replace($caret, new LBitOr($caret, $new, $this->indent));
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
            if ($arg instanceof LBitOr)
                $tokens[] = [...$tokens, ...$arg->tokens_bar_separated()];
            elseif ($arg instanceof LAngleBracket)
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
                $token = array_filter($token, fn($token) => $token->arg != 'rfl');
                $token = [...$token];
            }
        }
        if (count(
            array_unique(
                array_map(
                    fn($token) =>
                    $token instanceof LToken ?
                        $token->arg :
                        implode(',', array_map(fn($token) => $token->arg, $token)),
                    $tokens
                )
            )
        ) == 1) {
            $token = $tokens[0];
            if (is_array($token) && count($token) == 1)
                $token = $token[0];
            if (is_array($token))
                $token = new LArgsCommaSeparated(array_map(
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
        if ($this->parent instanceof LQuantifier)
            $syntax['setOf'] = true;
        return parent::latexArgs($syntax);
    }
}


class LPow extends LArithmetic
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
        if ($lhs instanceof LParenthesis) {
            if ($lhs->arg instanceof L_sqrt || $lhs->arg instanceof LPairedGroup || $lhs->arg instanceof LArgsSpaceSeparated && ($lhs->arg->is_Abs() || $lhs->arg->is_Bool()))
                $lhs = $lhs->arg;
        }

        if ($rhs instanceof LParenthesis)
            $rhs = $rhs->arg;
        return [$lhs->toLatex($syntax), $rhs->toLatex($syntax)];
    }
}


class L_ll extends LArithmetic
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


class L_gg extends LArithmetic
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


class LMod extends LArithmetic
{
    public static $input_priority = 71;
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

class LConstruct extends LArithmetic
{
    public static $input_priority = 68;
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

class LVConstruct extends LArithmetic
{
    public static $input_priority = 68;
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

class LAppend extends LArithmetic
{
    public static $input_priority = 66;
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

class L_sqcup extends LArithmetic
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

class L_sqcap extends LArithmetic
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

class L_cdotp extends LArithmetic
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

class L_circ extends LArithmetic
{
    public static $input_priority = 91;
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

class L_blacktriangleright  extends LArithmetic
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
        return $this->parent instanceof LArgsNewLineSeparated;
    }
}

abstract class LUnaryArithmetic extends LUnary {}

abstract class LUnaryArithmeticPost extends LUnaryArithmetic
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

abstract class LUnaryArithmeticPre extends LUnaryArithmetic
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

class LNeg extends LUnaryArithmeticPre
{
    public static $input_priority = 68;
    public function sep()
    {
        if ($this->arg instanceof LNeg)
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
        if ($arg instanceof LParenthesis) {
            if (
                $arg->arg instanceof LDiv ||
                $arg->arg instanceof LMul && !$arg->arg->command
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

class LPlus extends LUnaryArithmeticPre
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

class LInv extends LUnaryArithmeticPost
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

class L_sqrt extends LUnaryArithmeticPre
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
        if ($arg instanceof LParenthesis)
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

class LSquare extends LUnaryArithmeticPost
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
        if ($arg instanceof LParenthesis) {
            if ($arg->arg instanceof L_sqrt || $arg->arg instanceof LPairedGroup || $arg->arg instanceof LArgsSpaceSeparated && ($arg->arg->is_Abs() || $arg->arg->is_Bool()))
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

class LCubicRoot extends LUnaryArithmeticPre
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

class L_uparrow extends LUnaryArithmeticPre
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
        if ($arg instanceof LParenthesis && $arg->arg instanceof LArgsSpaceSeparated && $arg->arg->is_Abs())
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

class LUparrow extends LUnaryArithmeticPre
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

class LCube extends LUnaryArithmeticPost
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

class LQuarticRoot extends LUnaryArithmeticPre
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

class LTesseract extends LUnaryArithmeticPost
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

class LPipeForward extends LUnaryArithmeticPost
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

class LMethodChaining extends LBinary
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

abstract class LGetElemBase extends LBinary
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

    public function append_right($func)
    {
        if ($func == 'LBracket')
            return $this;
        return parent::append_right($func);
    }

    public function insert_comma($caret)
    {
        $new = new LCaret($this->indent);
        $this->rhs = new LArgsCommaSeparated([$caret, $new], $this->indent);
        return $new;
    }
}

class LGetElem extends LGetElemBase
{
    public function strFormat()
    {
        return '%s[%s]';
    }
    public function latexFormat()
    {
        return '%s_{%s}';
    }
}

class LGetElemQue extends LGetElemBase
{
    public function strFormat()
    {
        return '%s[%s]?';
    }
    public function latexFormat()
    {
        return '%s_{%s?}';
    }
}


class L_is extends LBinary
{
    public static $input_priority = 62;
    public function sep()
    {
        return ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LStatements;
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

class L_is_not extends LBinary
{
    public static $input_priority = 62;
    public function sep()
    {
        return ' ';
    }
    public function is_indented()
    {
        return $this->parent instanceof LStatements;
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

class L_setminus extends LBinary
{
    public static $input_priority = 71;
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

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

class L_cup extends LBinary
{
    public static $input_priority = 66;
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

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

class L_cap extends LBinary
{
    public static $input_priority = 71;
    public function sep()
    {
        return ' ';
    }

    public function strFormat()
    {
        return "%s $this->operator %s";
    }

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

abstract class LLogic extends LBinaryBoolean
{
    public $hanging_indentation;
    public function sep()
    {
        return $this->hanging_indentation ? "\n" . str_repeat(' ', $this->rhs->indent) : ' ';
    }

    public function is_indented()
    {
        return $this->parent instanceof LStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }
}


class LLogicAnd extends LLogic
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
        if ($this->lhs instanceof L_land) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
}


class LLogicOr extends LLogic
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
        if ($this->lhs instanceof L_lor) {
            return [$this->func => [...$lhs[$this->func], $rhs]];
        }

        return [$this->func => [$lhs, $rhs]];
    }
}

class L_lor extends LLogic
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($caret === $this->rhs && $caret instanceof LCaret) {
            if ($indent >= $this->indent) {
                if ($indent == $this->indent)
                    $indent = $this->indent + 2;
                $this->hanging_indentation = true;
                $caret->indent = $indent;
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }
}

class L_land extends LLogic
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


class L_subseteq extends LBinaryBoolean
{
    public static $input_priority = 51;

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

class L_supseteq extends LLogic
{
    public static $input_priority = 51;
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


class LStatements extends LArgs
{
    use LMultipleLine;
    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);

        if ($this->indent < $indent)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        for ($i = 0; $i < $newline_count; ++$i) {
            $caret = new LCaret($indent);
            $this->push($caret);
        }
        return $caret;
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LCaret) {
                $this->replace($caret, new LITE($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LColon::$input_priority;
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
        return implode("\n", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return implode("\n", array_fill(0, count($this->args), '{%s}'));
    }

    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof LCaret)
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
                    if ($parent instanceof LStatements)
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
                        if ($stmt instanceof L_lemma) {
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
                        if ($assignment instanceof LAssign) {
                            $proof = $assignment->rhs;
                            if ($proof instanceof L_by || $proof instanceof L_calc) {
                                $proof = $proof->arg;
                                if ($proof instanceof LStatements) {
                                    for ($i = $j + 1; $i <= $index; ++$i)
                                        $proof->push($this->args[$i]);
                                    array_splice($this->args, $j + 1, $index - $j);
                                    break;
                                }
                            } elseif ($proof instanceof LArgsNewLineSeparated) {
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
                foreach ($result as $echo)
                    $echo->parent = $this;
                array_splice($args, $index, 1, $result);
                $index += count($result) - 1;
            }
        }

        $tactic = $args[$index];
        if ($tactic instanceof LTactic || $tactic instanceof L_match) {
            if (($with = $tactic->with)) {
                if ($with->sep() == "\n") {
                    foreach ($with->args as $case)
                        $case->echo();
                } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator) {
                    if (($block = $sequential_tactic_combinator->arg) instanceof LTacticBlock)
                        $block->echo();
                    else
                        $sequential_tactic_combinator->echo();
                }
            } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator)
                $sequential_tactic_combinator->echo();
        } elseif ($tactic instanceof LTacticBlock)
            $tactic->echo();
        return $this;
    }

    public function isProp($vars)
    {
        $args = &$this->args;
        if (count($args) == 1)
            return $args[0]->isProp($vars);
    }
}


class LModule extends LStatements
{
    use LMultipleLine;
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
        if ($proof[0] instanceof LLineComment && $proof[0]->arg == 'proof')
            array_shift($proof);

        $proof = array_filter($proof, fn($stmt) => !($stmt instanceof LCaret));
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
                if ($stmt instanceof L_have || $stmt instanceof LTactic) {
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
            if ($caret instanceof LCaret) {
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
        $leanCode = $this->echo();
        $leanEchoFile = preg_replace('/\.lean$/', '.echo.lean', $leanFile);
        if (!file_exists($leanEchoFile)) {
            error_log("create new lean file = $leanEchoFile");
            std\createNewFile($leanEchoFile);
        }
        // create a block to write the code
        {
            $file = new std\Text($leanEchoFile);
            $codeStr = "$leanCode";
            $file->writelines([$codeStr]);
        }

        chdir(dirname(dirname(dirname(__FILE__))));
        $imports = array_filter(
            $leanCode->args,
            fn($import) =>
            $import instanceof L_import &&
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
        $cmd = $lakePath . ' env lean -D"linter.unusedTactic=false" -D"linter.dupNamespace=false" -D"diagnostics.threshold=1000" '. escapeshellarg($leanEchoFile);
        if (std\is_linux())
            exec($cmd, $output_array);
        else
            std\exec($cmd, $output_array, get_lean_env());
        $latex = [];
        $error = [];
        $leanCode->set_line(1);
        $end = end($leanCode->args);
        if ($end->line != substr_count("$leanCode", "\n") + 1) {
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
                $info = $matches[5];
                $error[] = [
                    'code' => $code,
                    'line' => $line, // later I will adjust this value.
                    'col' => $col - 2,
                    'type' => $matches[4],
                    'info' => $info
                ];
            } else
                $error[count($error) - 1]['info'] .= "\n" . $jsonline;
        }

        foreach ($leanCode->traverse() as $node) {
            if ($node instanceof LTactic && $node->func == 'echo')
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
            if (preg_match("/^ +echo /", $err['code']))
                $indicesToDelete[] = $i;
            else {
                $line = $err['line'];
                $err['line'] = $line - count(array_filter($keys, fn($key) => $key < $line)) - 1;
            }
        }
        if ($indicesToDelete) {
            foreach (array_reverse($indicesToDelete) as $i)
                array_splice($error, $i, 1);
        }

        array_shift($leanCode->args);
        $code = $leanCode->render2vue(true);
        array_push($code['error'], ...$error);
        return $code;
    }

    public function array_push(&$vars, $lhs, $rhs)
    {
        if ($lhs instanceof LToken) {
            $args = [$lhs, $rhs];
            while (($end = end($args)) instanceof L_rightarrow)
                array_splice($args, count($args) - 1, 2, [$end->lhs, $end->rhs]);
            $vars[] = $args;
        } elseif ($lhs instanceof LArgsSpaceSeparated) {
            foreach ($lhs->args as $lhs)
                $this->array_push($vars, $lhs, $rhs);
        }
    }
    public function parse_vars($implicit)
    {
        $vars = [];
        foreach ($implicit as $brace) {
            if ($brace instanceof LBrace) {
                $colon = $brace->arg;
                if ($colon instanceof LColon)
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
            if ($parenthesis instanceof LParenthesis) {
                $colon = $parenthesis->arg;
                if ($colon instanceof LColon)
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
        $def = [];
        $lemma = [];
        $date = [];
        $error = [];
        $comment = null;
        foreach ($this->args as $stmt) {
            if ($stmt instanceof L_import)
                $import[] = "$stmt->arg";
            elseif ($stmt instanceof L_lemma) {
                if ($stmt->assignment instanceof LAssign) {
                    $accessibility = $stmt->accessibility;
                    $declspec = $stmt->assignment->lhs;
                    if ($declspec instanceof LColon) {
                        if ($attribute = $stmt->attribute) {
                            $attribute = $attribute->arg;
                            if ($attribute instanceof LBracket) {
                                $attribute = $attribute->arg;
                                if ($attribute instanceof LArgsCommaSeparated)
                                    $attribute = array_map(fn($arg) => "$arg", $attribute->args);
                                elseif ($attribute instanceof LToken)
                                    $attribute = ["$attribute"];
                            }
                        }
                        $imply = $declspec->rhs->args;
                        if ($imply[0] instanceof LLineComment && $imply[0]->arg == 'imply')
                            array_shift($imply);

                        $proof = $stmt->assignment->rhs;
                        $by = $proof instanceof L_by ? 'by' : ($proof instanceof L_calc ? 'calc' : '');
                        $implyLean = preg_replace("/^  /m", "", implode("\n", array_map(fn($stmt) => "$stmt", $imply)));

                        if (count($imply) > 1 && $imply[0] instanceof L_let) {
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
                        if ($declspec instanceof LToken) {
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
                            if ($stmt instanceof LBracket) {
                                $instImplicit[] = "$stmt";
                                if ($stmt->arg instanceof LArgsSpaceSeparated) {
                                    if (count($stmt->arg->args) == 2) {
                                        [$lhs, $rhs] = $stmt->arg->args;
                                        if ($lhs instanceof LToken && $lhs->arg == "Decidable" && $rhs instanceof LToken)
                                            $decidables[] = "$rhs";
                                    }
                                }
                            } elseif ($stmt instanceof LBrace) {
                                $stmt->toLatex($syntax);
                                $implicit[] = $stmt;
                            } elseif ($stmt instanceof LArgsSpaceSeparated) {
                                if ($stmt->args[0] instanceof LBracket)
                                    $instImplicit[] = "$stmt";
                                elseif ($stmt->args[0] instanceof LBrace)
                                    $implicit[] = $stmt;
                                else
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "lemma $name is not well-defined",
                                        'type' => 'linter'
                                    ];
                            } elseif ($stmt instanceof LLineComment) {
                                if ($stmt->arg == 'given') {
                                    $given = $i + 1;
                                    break;
                                }
                                if ($implicit)
                                    $implicit[] = "$stmt";
                                else
                                    $instImplicit[] = "$stmt";
                            } elseif ($stmt instanceof LParenthesis) {
                                // the given comment is missing, try to add one
                                if ($stmt->arg instanceof LColon) {
                                    std\array_insert($stmt->parent->args, $i, new LLineComment('given', $stmt->indent, $stmt->parent));
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
                                if ($stmt instanceof LParenthesis) {
                                    $colon = $stmt->arg;
                                    if ($colon instanceof LColon) {
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
                                    } elseif ($colon instanceof LAssign) {
                                        $pivot = $i;
                                        break;
                                    }
                                } elseif ($stmt->is_comment())
                                    $latex[] = null;
                                elseif ($stmt instanceof LBrace) {
                                    $pivot = $i;
                                    $given[$pivot] = new LParenthesis($stmt->arg, $stmt->indent, $stmt->parent);
                                    break;
                                } elseif ($stmt instanceof LCaret) {
                                    $indicesToDelete[] = $i;
                                } else {
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "given statement must be of LParenthesis Type",
                                        'type' => 'linter'
                                    ];
                                }
                            }
                            if ($indicesToDelete) {
                                foreach (array_reverse($indicesToDelete) as $index)
                                    array_splice($given, $index, 1);
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
                        $proof = $by ? ["$by" => self::merge_proof($proof->arg, $echo, $syntax)] : self::merge_proof($proof, $echo, $syntax);
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
                            'info' => "declspec of lemma must be of LColon Type",
                            'type' => 'linter'
                        ];
                } else
                    $error[] = [
                        'code' => "$stmt",
                        'line' => 0,
                        'info' => "lemma must be of LAssign Type",
                        'type' => 'linter'
                    ];
            } elseif ($stmt instanceof L_def)
                $def[] = "$stmt";
            elseif ($stmt instanceof L_open) {
                $stmt = $stmt->arg;
                if ($stmt instanceof LArgsSpaceSeparated) {
                    if (count($stmt->args) == 2 && $stmt->args[1] instanceof LParenthesis) {
                        $defs = $stmt->args[1]->arg;
                        $open[] = [
                            $stmt->args[0]->__toString() =>
                            $defs instanceof LArgsSpaceSeparated ?
                                array_map(fn($arg) => "$arg", $defs->args) :
                                ["$defs->arg"]
                        ];
                    } else
                        $open[] = array_map(fn($arg) => "$arg", $stmt->args);
                } else
                    $open[] = ["$stmt->arg"];
            } elseif ($stmt instanceof LLineComment) {
                if (preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', "$stmt->arg", $matches))
                    $date[$matches[1]] = $matches[2];
                else
                    $comment = "$stmt->arg";
            } elseif ($stmt instanceof LBlockComment)
                $comment = "$stmt->arg";
        }

        return [
            'imports' => $import,
            'open' => $open,
            'def' => $def,
            'lemma' => $lemma,
            'date' => $date,
            'error' => $error,
        ];
    }

    public function import($module)
    {
        $this->unshift(new L_import(
            array_reduce(
                preg_split('/\./', $module),
                function ($carry, $token) {
                    $token = new LToken($token, 0);
                    return $carry ? new LProperty($carry, $token, 0) : $token;
                },
            ),
            0
        ));
    }

    public function echo()
    {
        $args = &$this->args;
        $this->import('sympy.Basic');
        for ($index = 0; $index < count($args); ++$index)
            $args[$index] = $args[$index]->echo();

        return $this;
    }
}

abstract class LCommand extends LUnary
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

class L_import extends LCommand
{
    public function append_attr($caret)
    {
        if ($caret == $this->arg) {
            $new = new LCaret($this->indent);
            $this->arg = new LProperty($this->arg, $new, $this->indent);
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
            $new = new LCaret($this->indent);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class L_open extends LCommand
{
    public function append_attr($caret)
    {
        if ($caret == $this->arg) {
            $new = new LCaret($this->indent);
            $this->arg = new LProperty($this->arg, $new, $this->indent);
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
            $new = new LCaret($this->indent);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class L_namespace extends LCommand
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


class LBar extends LUnary
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
                //must be >= LAssign::$input_priority
                return LAssign::$input_priority;
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
        return $this;
    }

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LStatements) {
                $arrow->rhs = new LCaret($arrow->indent);
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
            $new = new LCaret($this->indent);
            $this->replace($caret, new LArgsCommaSeparated([$caret, $new], $this->indent));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LRightarrow extends LBinary
{
    public static $input_priority = 20; // same as LColon::$input_priority;
    public function sep()
    {
        return $this->rhs instanceof LStatements ? "\n" : ($this->rhs instanceof LCaret ? '' : ' ');
    }

    public function is_indented()
    {
        return false;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        $lhs = "%s";
        if (!($this->lhs instanceof LCaret))
            $lhs .= ' ';
        return "$lhs$this->operator$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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
        if (($parent = $this->parent) instanceof LBar && ($parent = $parent->parent) instanceof L_with && (($parent = $parent->parent) instanceof L_match || $parent instanceof LTactic && $parent->func == 'induction')) {
            $token[] = new LToken('main', $this->rhs->indent);
            $subject = $parent->args[0];
            if ($subject instanceof LArgsCommaSeparated) {
                foreach ($subject->args as $sujet) {
                    if ($sujet instanceof LColon)
                        $token[] = $sujet->lhs;
                }
            } else if ($subject instanceof LColon)
                $token[] = $subject->lhs;
        }
        $expr = $this->lhs;
        if ($expr instanceof LArgsSpaceSeparated) {
            if ($expr->args[0] instanceof LToken)
                $func = $expr->args[0]->arg;
            elseif ($expr->args[0] instanceof LProperty && $expr->args[0]->lhs instanceof LCaret && $expr->args[0]->rhs instanceof LToken)
                $func = $expr->args[0]->rhs->arg;
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
        } elseif ($expr instanceof LAngleBracket) {
            if ($expr->arg instanceof LArgsCommaSeparated)
                // | ⟨v, property⟩ =>
                array_push($token, ...array_slice($expr->arg->args, 1));
        } elseif ($expr instanceof LArgsCommaSeparated) {
            // | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
            foreach ($expr->args as $arg) {
                if ($arg instanceof LAngleBracket && $arg->arg instanceof LArgsCommaSeparated)
                    $token[] = $arg->arg->args[1];
            }
        }

        $stmt = $this->rhs;
        $stmt->echo();
        if ($token && $stmt instanceof LStatements) {
            $indent = $stmt->args[0]->indent;
            if (count($token) > 1)
                $token = new LArgsCommaSeparated(
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
            $stmt->unshift(new LTactic('echo', $token, $indent));
        }
        return $this;
    }

    public function insert($caret, $func, $type)
    {
        if ($this->rhs === $caret) {
            if ($caret instanceof LCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }
}

class L_rightarrow extends LBinary
{
    public static $input_priority = 25; // right associative operator
    public function sep()
    {
        return $this->rhs instanceof LStatements ? "\n" : ' ';
    }

    public function is_indented()
    {
        return $this->parent instanceof LStatements;
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "%s $this->operator$sep%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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
        return ($lhs instanceof LToken && (($vars["$lhs"] ?? 'Prop') == 'Prop') || $lhs->isProp($vars)) &&
            ($rhs instanceof LToken && (($vars["$rhs"] ?? 'Prop') == 'Prop') || $rhs->isProp($vars));
    }
}

class L_mapsto extends LBinary
{
    public function sep()
    {
        return $this->rhs instanceof LStatements ? "\n" : ' ';
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->rhs) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->rhs = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->rhs->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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

class L_leftarrow extends LUnary
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

class L_lnot extends LUnary
{
    public static $input_priority = 50;
    public function is_indented()
    {
        return $this->parent instanceof LStatements;
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    use LProp;

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

class L_match extends LArgs
{
    public function __construct($subject, $indent, $parent = null)
    {
        parent::__construct([$subject], $indent, $parent);
    }

    public function insert($caret, $func, $type)
    {
        if (!$this->with && $func == 'L_with') {
            $caret = new LCaret($this->indent);
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
                return LColon::$input_priority - 1;
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
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->subject) {
            $caret = new LCaret($this->indent);
            $this->subject = new LArgsCommaSeparated([$this->subject, $caret], $this->indent);
            return $caret;
        }
        if ($this->parent)
            return $this->parent->insert_comma($this);
    }

    public function relocate_last_comment()
    {
        $with = $this->with;
        if ($with instanceof L_with)
            $with->relocate_last_comment();
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LCaret)
            return $this->insert_token($caret, $token);
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
        if ($case instanceof LBar) {
            $rightarrow = $case->arg;
            if ($rightarrow instanceof LRightarrow)
                return $rightarrow->rhs->isProp($vars);
        }
    }
}

class LITE extends LArgs
{
    public static $input_priority = 60;
    public function __construct($if, $indent, $parent = null)
    {
        parent::__construct([$if], $indent, $parent);
    }

    public function insert_then($caret)
    {
        if (!$this->then) {
            $caret = new LCaret($this->indent + 2);
            $this->then = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function insert_else($caret)
    {
        if (!$this->else) {
            $caret = new LCaret($this->indent + 2);
            $this->else = $caret;
            return $caret;
        }
        if ($this->parent)
            return $this->parent->insert_else($this);
    }

    public function insert_if($caret)
    {
        if ($caret instanceof LCaret) {
            if ($caret === $this->else) {
                $this->else = new LITE($caret, $this->indent);
                return $caret;
            }
            if ($caret === $this->then) {
                $this->then = new LITE($caret, $this->indent + 2);
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($caret === $this->then || $caret === $this->else && $caret instanceof LCaret)
            return $caret;
        if ($this->parent)
            return $this->parent->insert_newline($this, $newline_count, $indent, $next_token);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LStatements || $parent instanceof LITE && $this === $parent->then;
    }

    public function strFormat()
    {
        $else = $this->else;
        $indent_else = str_repeat(' ', $this->indent);
        $sep = $else instanceof LITE ? ' ' : "\n";
        return "if %s then\n%s\n{$indent_else}else$sep%s";
    }

    public function latexFormat()
    {
        $cases = 0;
        $else = $this;
        while (true) {
            [$if, $then, $else] = $else->strip_parenthesis();
            ++$cases;

            if (!($else instanceof LITE))
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

            if (!($else instanceof LITE))
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
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
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
        if (!($else instanceof LITE))
            ++$line;
        return $else->set_line($line);
    }
}

class LArgsSpaceSeparated extends LArgs
{
    public static $input_priority = 72;
    public function is_space_separated()
    {
        return true;
    }

    public function tokens_space_separated()
    {
        $tokens = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LToken)
                $tokens[] = $arg;
            elseif ($arg instanceof LAngleBracket)
                $tokens[] = $arg->tokens_comma_separated();
            else
                return [];
        }
        return $tokens;
    }

    public function unique_token($indent)
    {
        if ($tokens = $this->tokens_space_separated()) {
            if (count(array_unique(array_map(fn($token) => $token->arg, $tokens))) == 1) {
                $token = clone $tokens[0];
                $token->indent = $indent;
                return $token;
            }
        }
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LStatements ||
            $parent instanceof LArgsCommaNewLineSeparated ||
            $parent instanceof LArgsNewLineSeparated ||
            $parent instanceof LITE && ($this === $parent->then || $this === $parent->else);
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
        if ($func instanceof LToken) {
            switch (count($args)) {
                case 2:
                    switch ($func->arg) {
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
                            return "\\$func->arg {%s}";
                        case 'arcsec':
                        case 'arccsc':
                        case 'arccot':
                        case 'arcsinh':
                        case 'arccosh':
                        case 'arctanh':
                        case 'arccoth':
                            return "$func->arg\\ {%s}";

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
                    switch ($func->arg) {
                        case 'Ioc':
                            return '\left(%s, %s\right]';
                        case 'Ioo':
                            return '\left(%s, %s\right)';
                        case 'Icc':
                            return '\left[%s, %s\right]';
                        case 'Ico':
                            return '\left[%s, %s\right)';
                    }
                    break;
            }
        } elseif ($this->is_Bool()) {
            return '\left|{%s}\right|';
        } elseif ($func instanceof LProperty) {
            if ($func->rhs instanceof LToken) {
                switch ($func->rhs->arg) {
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
        return $func instanceof LToken && count($args) == 2 && $func->arg == 'abs';
    }
    public function is_Bool()
    {
        $args = $this->args;
        $func = $args[0];
        return $func instanceof LProperty && $func->rhs instanceof LToken && $func->rhs->arg == 'toNat' && $func->lhs instanceof LToken && $func->lhs->arg == 'Bool';
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
        if ($func instanceof LToken) {
            $func = $func->arg;
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
                            if ($arg instanceof LParenthesis && $arg->arg instanceof LDiv)
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

    public function insert_token($caret, $word)
    {
        $new = new LToken($word, $this->indent);
        $this->push($new);
        return $new;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 72;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_unary($caret, $func)
    {
        if ($caret === end($this->args)) {
            $indent = $this->indent;
            if ($caret instanceof LCaret) {
                $new = new $func($caret, $indent);
                $this->replace($caret, $new);
            } else {
                $caret = new LCaret($indent);
                $new = new $func($caret, $indent);
                $this->push($new);
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function get_type($vars, $arg)
    {
        if ($arg instanceof LToken)
            return $vars["$arg"] ?? '';
        if ($arg instanceof LArgsSpaceSeparated) {
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
    }

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args) && !$caret instanceof LCaret && $type != 'modifier') {
            $caret = new LCaret($this->indent);
            $this->push(new $func($caret, $caret->indent));
            return $caret;
        } else if ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }
}

class LArgsNewLineSeparated extends LArgs
{
    use LMultipleLine;
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);

        if ($this->indent < $indent) {
            $end = end($this->args);
            if ($end instanceof LToken || $end instanceof LProperty) {
                // function call
                $caret = new LCaret($indent);
                $new = new LArgsNewLineSeparated([$caret], $indent);
                $caret = $new->push_newlines($newline_count - 1);
                $this->replace($end, new LArgsIndented($end, $new, $this->indent));
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent instanceof LAssign && !($caret instanceof LLineComment))
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);
        else {

            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LCaret($indent);
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
                if ($this->parent instanceof L_calc)
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
            if ($end instanceof LCaret || $end->is_comment()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LStatements)
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
            $this->push(new LCaret($this->indent));
        }
        return end($this->args);
    }
}

class LArgsIndented extends LBinary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);

        if ($this->indent < $indent) {
            $end = end($this->args);
            if ($end instanceof LToken || $end instanceof LProperty) {
                // function call
                $caret = new LCaret($indent);
                $new = new LArgsNewLineSeparated([$caret], $indent);
                $caret = $new->push_newlines($newline_count - 1);
                $this->replace($end, new LArgsIndented($end, $new, $this->indent));
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } elseif ($this->parent instanceof LAssign)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);
        else {

            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count; ++$i) {
                    $caret = new LCaret($indent);
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
                if ($this->parent instanceof L_calc)
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
            if ($end instanceof LCaret || $end->is_comment()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LStatements)
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

class LArgsCommaSeparated extends LArgs
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
                if ($this->parent instanceof LBar)
                    return LColon::$input_priority;
                return LColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        $caret = new LCaret($this->indent);
        $this->push($caret);
        return $caret;
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LCaret)
            return $this->insert_token($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LCaret) {
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
            if ($arg instanceof LToken)
                $tokens[] = $arg;
            elseif ($arg instanceof LAngleBracket)
                array_push($tokens, ...$arg->tokens_comma_separated());
        }
        return $tokens;
    }
}

class LArgsCommaNewLineSeparated extends LArgs
{
    use LMultipleLine;
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            if (end($this->args) === $caret) {
                for ($i = 0; $i < $newline_count - 1; ++$i) {
                    $caret = new LCaret($indent);
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
        $caret = new LCaret($this->indent);
        $this->push($caret);
        return $caret;
    }


    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LCaret) {
                $this->replace($caret, new $func($caret, $caret->indent));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


abstract class LSyntax extends LArgs
{
    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'arg':
                $this->args[0] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args)) {
            $caret = new LCaret($this->indent);
            $this->push(new $func($caret, $this->indent));
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class LTactic extends LSyntax
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
        return $this->append_line_comment($comment);
    }

    public function append_line_comment($comment)
    {
        $new = new LLineComment($comment, $this->indent);
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
                if ($this->parent instanceof L_by)
                    return LColon::$input_priority;
                return LAssign::$input_priority;
            case 'arg':
                return $this->args[0];
            case 'modifiers':
                return array_slice($this->args, 1);
            case 'at':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof L_at)
                        return $args[$index];
                }
                return;
            case 'with':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof L_with)
                        return $args[$index];
                }
                return;
            case 'sequential_tactic_combinator':
                $args = &$this->args;
                for ($index = count($args) - 1; $index >= 0; --$index) {
                    if ($args[$index] instanceof LSequentialTacticCombinator)
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
        return !$parent || $parent instanceof LStatements || $parent instanceof LSequentialTacticCombinator && $this->indent > $parent->indent;
    }

    public function strFormat()
    {
        $func = $this->func;
        if ($this->only)
            $func .= " only";
        if (!($this->arg instanceof LCaret))
            $func .= ' ';
        return $func . implode(' ', array_fill(0, count($this->args), "%s"));
    }

    public function latexFormat()
    {
        return $this->strFormat();
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
        if ($arg instanceof LRightarrow || $arg instanceof L_with)
            $arg->relocate_last_comment();
    }

    public function insert_only($caret)
    {
        if ($caret === end($this->args)) {
            $this->only = true;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function has_tactic_block_followed()
    {
        // check the next statement:
        // if the next statement is a tactic block, skipping echoing main since it will be done in the next tactic block
        // if the next statement isn't a tactic block, echo main as usual
        if ($this->parent instanceof LStatements) {
            $stmts = $this->parent->args;
            for ($index = std\index($stmts, $this) + 1; $index < count($stmts); ++$index) {
                $stmt = $stmts[$index];
                if ($stmt instanceof LTacticBlock)
                    return true;
                if (!$stmt->is_comment())
                    break;
            }
        }
    }

    public function get_echo_token()
    {
        if ($this->at) {
            $token = $this->at->arg;
            if ($token instanceof LArgsSpaceSeparated)
                $token = new LArgsCommaSeparated(
                    array_map(fn($arg) => clone $arg, $token->args),
                    $this->indent
                );
        } else {
            $token = [];
            $main = "main";
            switch ($this->func) {
                case 'intro':
                case 'by_contra':
                    $arg = $this->arg;
                    if ($arg instanceof LToken)
                        $token[] = clone $arg;
                    else if ($arg instanceof LArgsSpaceSeparated) {
                        foreach ($arg->tokens_space_separated() as $arg) {
                            if ($arg instanceof LToken)
                                $token[] = clone $arg;
                            else if (is_array($arg)) {
                                foreach ($arg as $a)
                                    $token[] = clone $a;
                            }
                        }
                    }
                    else if ($arg instanceof LAngleBracket) {
                        $arg = $arg->arg;
                        if ($arg instanceof LToken)
                            $token[] = clone $arg;
                        else if ($arg instanceof LArgsCommaSeparated)
                            $token = array_map(fn($arg) => clone $arg, $arg->args);
                    }
                    break;
                case 'denote':
                case "denote'":
                    if ($this->arg instanceof LColon) {
                        $var = $this->arg->lhs;
                        if ($var instanceof LToken)
                            $token[] = clone $var;
                    }
                    $main = null;
                    break;
                case 'by_cases':
                    if ($this->arg instanceof LColon) {
                        $var = $this->arg->lhs;
                        if ($var instanceof LToken) {
                            if ($this->has_tactic_block_followed())
                                return;
                            $token[] = clone $var;
                        }
                    }
                    break;
                case 'split_ifs':
                    if (($with = $this->with) && $with->sep() == ' ') {
                        $var = $with->args[0];
                        $var = $var->tokens_space_separated();
                        if ($var) {
                            if ($this->has_tactic_block_followed())
                                return;
                            $token[] = clone $var[0];
                        }
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
                case 'rcases':
                    if (($with = $this->with) && ($tokens = $with->tokens_bar_separated())) {
                        if ($this->has_tactic_block_followed())
                            return;
                        foreach ($tokens as $arg) {
                            if (is_array($arg))
                                array_push($token, ...array_filter($arg, fn($token) => $token->arg != 'rfl'));
                            else if ($arg->arg != 'rfl')
                                $token[] = $arg;
                            break;
                        }
                    }
                    break;
                case 'sorry':
                    return;
            }

            if ($this->has_tactic_block_followed() || $this->parent instanceof LSequentialTacticCombinator);
            else if ($main)
                $token[] = new LToken($main, $this->indent);
            switch (count($token)) {
                case 0:
                    break;
                case 1:
                    $token = $token[0];
                    break;
                default:
                    $token = new LArgsCommaSeparated(
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
        if ($token)
            return [
                $this,
                new LTactic('echo', $token, $this->indent)
            ];
        return $this;
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
            if ($block instanceof LTacticBlock) {
                if ($block->arg instanceof LStatements) {
                    $statements = $block->arg->args;
                    $block->arg = new LCaret($block->indent);
                    $array = [$this];
                    foreach ($statements as $stmt)
                        array_push($array, ...$stmt->split($syntax));
                    return $array;
                }
            }
        }
        return [$this];
    }

    public function insert_sequential_tactic_combinator($caret)
    {
        if ($caret === end($this->args)) {
            $caret = new LCaret($this->indent);
            $this->push(new LSequentialTacticCombinator($caret, $this->indent));
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret === end($this->args) && $caret instanceof LCaret) {
            if ($this->func == 'try') {
                $caret->parent->replace($caret, new LTactic($type, $caret, $this->indent));
                return $caret;
            } else
                return $this->insert_token($caret, $type);
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->arg && $caret instanceof LArgsSpaceSeparated) {
                $new = new LCaret($this->indent);
                $caret->push($new);
                return $new;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function insert_comma($caret)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LToken) {
                $new = new LCaret($this->indent);
                $this->replace($caret, new LArgsCommaSeparated([$caret, $new], $this->indent));
                return $new;
            }
            if ($caret instanceof LArgsCommaSeparated) {
                $new = new LCaret($this->indent);
                $caret->push($new);
                return $new;
            }
        }
        return parent::insert_comma($caret);
    }
}

class L_by extends LUnary
{
    public function is_indented()
    {
        return $this->parent instanceof LArgsCommaNewLineSeparated;
    }
    public function sep()
    {
        return $this->arg instanceof LStatements ? "\n" : ' ';
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->operator$sep%s";
    }
    public function latexFormat()
    {
        $sep = $this->sep();
        return "$this->command\\ %s";
    }
    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function echo()
    {
        $this->arg = $this->arg->echo();
        return $this;
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LStatements)
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
}

class L_from extends LUnary
{
    public function is_indented()
    {
        return $this->parent instanceof LArgsCommaNewLineSeparated;
    }
    public function sep()
    {
        return $this->arg instanceof LStatements ? "\n" : ' ';
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
    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function relocate_last_comment()
    {
        $this->arg->relocate_last_comment();
    }

    public function echo()
    {
        $this->arg = $this->arg->echo();
        return $this;
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LStatements)
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

class L_calc extends LUnary
{
    public function is_indented()
    {
        return false;
    }

    public function sep()
    {
        return $this->arg instanceof LArgsNewLineSeparated ? "\n" : ' ';
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LArgsNewLineSeparated([$caret], $indent);
            return $this->arg->push_newlines($newline_count - 1);
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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
        if ($this->arg instanceof LArgsNewLineSeparated)
            ++$line;
        return $this->arg->set_line($line);
    }
}


class L_MOD extends LUnary
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


class L_using extends LUnary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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

class L_at extends LUnary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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

class LIn extends LUnary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'in';
            default:
                return parent::__get($vname);
        }
    }
}

class L_generalizing extends LUnary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent <= $indent && $caret instanceof LCaret && $caret === $this->arg) {
            if ($indent == $this->indent)
                $indent = $this->indent + 2;
            $caret->indent = $indent;
            $this->arg = new LStatements([$caret], $indent);
            for ($i = 1; $i < $newline_count; ++$i) {
                $caret = new LCaret($indent);
                $this->arg->push($caret);
            }
            return $caret;
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
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

class LSequentialTacticCombinator extends LUnary
{
    public function is_indented()
    {
        return false;
    }

    public function sep()
    {
        return $this->arg instanceof LTacticBlock || $this->arg->indent > $this->indent ? "\n" : ' ';
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
        if ($caret instanceof LCaret) {
            $this->arg = new LTactic($type, $caret, $caret->indent);
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($caret instanceof LCaret && $caret === $this->arg) {
            if ($next_token == '·') {
                if ($indent == $this->indent)
                    return $caret;
            } else {
                if ($indent == $this->indent)
                    $indent += 2;
                $caret->indent = $indent;
                return $caret;
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function echo()
    {
        if ($this->arg instanceof LTacticBlock)
            $this->arg = $this->arg->echo();
        return $this;
    }

    public function set_line($line)
    {
        $this->line = $line;
        if ($this->arg instanceof LTacticBlock || $this->arg->indent > $this->indent)
            ++$line;
        return $this->arg->set_line($line);
    }
}

class LTacticBlock extends LUnary
{
    public function is_indented()
    {
        return true;
    }

    public function strFormat()
    {
        return "$this->operator\n%s";
    }

    public function latexFormat()
    {
        return "$this->command\n%s";
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($caret === $this->arg) {
            if ($caret instanceof LCaret) {
                if ($this->indent <= $indent) {
                    if ($indent == $this->indent)
                        $indent = $this->indent + 2;
                    $caret->indent = $indent;
                    $this->arg = new LStatements([$caret], $indent);
                    for ($i = 1; $i < $newline_count; ++$i) {
                        $caret = new LCaret($indent);
                        $this->arg->push($caret);
                    }
                    return $caret;
                }
            } elseif ($caret instanceof LStatements) {
                $block = $caret;
                if ($indent >= $block->indent) {
                    for ($i = 0; $i < $newline_count; ++$i) {
                        $caret = new LCaret($block->indent);
                        $block->push($caret);
                    }
                    return $caret;
                }
            } else if ($this->indent < $indent) {
                $caret = new LCaret($indent);
                $this->arg->indent = $indent;
                $this->arg = new LStatements([$this->arg, $caret], $indent);
                return $caret;
            }
        }

        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function insert_line_comment($caret, $comment)
    {
        if ($caret instanceof LCaret) {
            $indent = $this->indent + 2;
            $new = new LLineComment($comment, $indent);
            $this->arg = new LStatements([$new], $indent);
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
        $this->arg = $statements->echo();
        if ($statements instanceof LStatements) {
            if ($this->parent instanceof LSequentialTacticCombinator) {
                if (
                    $this->parent->parent instanceof LTactic &&
                    ($with = $this->parent->parent->with) &&
                    ($token = $with->unique_token($statements->indent))
                );
                else
                    $token = new LToken('main', $statements->indent);
                $statements->unshift(new LTactic('echo', $token, $statements->indent));
            } elseif ($this->parent instanceof LStatements) {
                $index = std\index($this->parent->args, $this);
                $tacticBlockCount = 0;
                for ($i = $index - 1; $i >= 0; --$i) {
                    $stmt = $this->parent->args[$i];
                    if ($stmt->is_comment())
                        continue;

                    if ($stmt instanceof LTacticBlock) {
                        ++$tacticBlockCount;
                        continue;
                    }

                    if ($stmt instanceof LTactic) {
                        if ($stmt->func == 'echo')
                            continue;
                        switch ($stmt->func) {
                            case 'rcases':
                                if (($with = $stmt->with) instanceof L_with && ($tokens = $with->tokens_bar_separated())) {
                                    $token = $tokens[$tacticBlockCount];
                                    $indent = $statements->indent;
                                    if (is_array($token)) {
                                        $token = array_filter($token, fn($token) => $token->arg != 'rfl');
                                        $token = [...$token];
                                        $token = array_map(function ($token) use ($indent) {
                                            $token = clone $token;
                                            $token->indent = $indent;
                                            return $token;
                                        }, $token);
                                        if (count($token) == 1)
                                            [$token] = $token;
                                        else
                                            $token = new LArgsCommaSeparated($token, $indent);
                                    } else {
                                        $token = clone $token;
                                        $token->indent = $indent;
                                    }
                                    $statements->unshift(new LTactic(
                                        'echo',
                                        $token,
                                        $indent,
                                    ));
                                }
                                break;
                            case "cases'":
                                if (($with = $stmt->with) instanceof L_with && ($tokens = $with->tokens_space_separated())) {
                                    $token = $tokens[$tacticBlockCount];
                                    $token = clone $token;
                                    $token->indent = $statements->indent;
                                    $statements->unshift(new LTactic(
                                        'echo',
                                        $token,
                                        $statements->indent,
                                    ));
                                }
                                break;
                            case 'split_ifs':
                                if (($with = $stmt->with) instanceof L_with && count($with->args) == 1 && (($tokens = $with->args[0]) instanceof LArgsSpaceSeparated || $tokens instanceof LToken)) {
                                    $statements->unshift(new LTactic(
                                        'echo',
                                        new LToken(
                                            'main',
                                            $statements->indent
                                        ),
                                        $statements->indent,
                                    ));
                                    $tokens = $tokens->tokens_space_separated();
                                    $token = $tokens[$tacticBlockCount] ?? null;
                                    if ($token) {
                                        $token = clone $token;
                                        $token->indent = $this->indent;
                                        $echo = new LTactic(
                                            'echo',
                                            $token,
                                            $this->indent
                                        );
                                        return [$echo, $this, clone $echo];
                                    }
                                }
                                break;

                            case 'by_cases':
                                if (($colon = $stmt->arg) instanceof LColon && ($token = $colon->lhs) instanceof LToken) {
                                    $tokens = $token->tokens_space_separated();
                                    $token = $tokens[$tacticBlockCount] ?? null;
                                    if ($token) {
                                        $token = clone $token;
                                        $token->indent = $this->indent;
                                        $echo = new LTactic(
                                            'echo',
                                            $token,
                                            $this->indent
                                        );
                                        return [$echo, $this, clone $echo];
                                    }
                                }
                                break;
                            default:
                                $token = new LToken('main', $statements->indent);
                                $sequential_tactic_combinator = $stmt->sequential_tactic_combinator;
                                if ($sequential_tactic_combinator) {
                                    $tactic = $sequential_tactic_combinator->arg;
                                    $tactic_token = $tactic->get_echo_token();
                                    if ($tactic_token) {
                                        if ($tactic_token instanceof LArgsCommaSeparated) {
                                            $tactic_token->push($token);
                                            $token = $tactic_token;
                                        } else
                                            $token = new LArgsCommaSeparated([$tactic_token, $token], $statements->indent);
                                    }
                                }
                                $statements->unshift(new LTactic(
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
        return $this;
    }

    public function set_line($line)
    {
        $this->line = $line;
        ++$line;
        return $this->arg->set_line($line);
    }

    public function split(&$syntax = null)
    {
        if ($this->arg instanceof LStatements) {
            $statements = $this->arg->args;
            $self = clone $this;
            $self->arg = new LCaret($this->indent);
            $array = [$self];
            foreach ($statements as $stmt)
                array_push($array, ...$stmt->split($syntax));
            return $array;
        }
        return [$this];
    }
}


class L_with extends LArgs
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
        return $caret instanceof LCaret || $caret->tokens_space_separated() || $caret instanceof LBitOr ? ' ' : "\n";
    }

    public function strFormat()
    {
        $sep = $this->sep();
        return "$this->func$sep" . implode("\n", array_fill(0, count($this->args), '%s'));
    }

    public function latexFormat()
    {
        return $this->strFormat();
    }

    public function relocate_last_comment()
    {
        end($this->args)->relocate_last_comment();
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next_token);

        $cases = $this->args;
        if (count($cases) > 0) {
            $caret = end($cases);
            if ($caret instanceof LCaret)
                return $caret;

            if ($next_token == '|') {
                if ($caret instanceof LBar || $caret->is_comment()) {
                    $caret = new LCaret($this->indent);
                    $this->push($caret);
                    return $caret;
                }
            }
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function insert_bar($caret, $prev_token, $next_token)
    {
        $cases = $this->args;
        if (end($cases) === $caret) {
            if ($caret instanceof LCaret) {
                $this->replace($caret, new LBar($caret, $this->indent));
                return $caret;
            } else {
                $new = new LCaret($this->indent);
                $this->replace($caret, new LBitOr($caret, $new, $this->indent));
                return $new;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LCaret)
            return $this->insert_token($caret, $token);
        return parent::insert_tactic($caret, $token);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof L_match)
                    return 23;
                return 17;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LCaret($this->indent);
            $this->replace($caret, new LArgsCommaSeparated([$caret, $new], $this->indent));
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
        if (count($this->args) == 1 && $this->args[0] instanceof LBitOr)
            return $this->args[0]->tokens_bar_separated();
        return [];
    }

    public function unique_token($indent)
    {
        if (count($this->args) == 1) {
            $stmt = $this->args[0];
            if ($stmt instanceof LBitOr || $stmt instanceof LArgsSpaceSeparated)
                return $stmt->unique_token($indent);
        }
    }

    public function tokens_space_separated()
    {
        if (count($this->args) == 1 && $this->args[0] instanceof LArgsSpaceSeparated)
            return $this->args[0]->tokens_space_separated();
        return [];
    }
}

class LAttribute extends LUnary
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

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        return $caret;
    }

    public function append($new, $type)
    {
        return $this->append_accessibility($new, "public");
    }

    public function append_accessibility($new, $accessibility)
    {
        switch ($new) {
            case 'L_theorem':
            case 'L_lemma':
            case 'L_def':
                $caret = new LCaret($this->indent);
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


class L_def extends LArgs
{
    public $accessibility;
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
            $this->func => parent::jsonSerialize(),
            "accessibility" => $this->accessibility
        ];
        if ($this->attribute)
            $json['attribute'] = $this->attribute->jsonSerialize();
        return $json;
    }

    public function insert_newline($caret, $newline_count, $indent, $next_token)
    {
        if ($this->indent < $indent) {
            if ($caret === $this->assignment) {
                if ($caret instanceof LToken || $caret instanceof LProperty) {
                    $caret = new LCaret($indent);
                    $new = new LArgsNewLineSeparated([$caret], $indent);
                    $caret = $new->push_newlines($newline_count - 1);
                    $this->assignment = new LArgsIndented(
                        $this->assignment,
                        $new,
                        $this->indent
                    );
                    return $caret;
                }
                if ($caret instanceof LColon) {
                    if ($caret->rhs instanceof LCaret) {
                        $caret = $caret->rhs;
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LStatements([$caret], $indent);
                        return $caret;
                    }
                } elseif ($caret instanceof LAssign) {
                    $caret = $this->assignment->rhs;
                    if ($caret instanceof LCaret) {
                        $caret->indent = $indent;
                        $this->assignment->rhs = new LStatements([$caret], $indent);
                        return $caret;
                    } else
                        return parent::insert_newline($caret, $newline_count, $this->indent, $next_token);
                }
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next_token);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            case 'attribute':
                return $this->args[0] ?? null;
            case 'assignment':
                return $this->args[1] ?? null;
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
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function relocate_last_comment()
    {
        $assignment = $this->assignment;
        if ($assignment instanceof LAssign)
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
        return $this->insert_token($caret, $token);
    }
}


class L_theorem extends L_def {}


class L_lemma extends L_def
{
    public function echo()
    {
        $this->assignment = $this->assignment->echo();
        if ($this->assignment instanceof LAssign && $this->assignment->rhs instanceof L_by) {
            $statement = $this->assignment->rhs->arg;
            if ($statement instanceof LStatements) {
                $statements = &$statement->args;
                for ($i = count($statements) - 1; $i >= 0; --$i) {
                    $stmt = $statements[$i];
                    if ($stmt->is_comment())
                        continue;
                    if ($stmt instanceof LTactic || $stmt instanceof L_have || $stmt instanceof L_let) {
                        $token = $stmt->get_echo_token();
                        // try echo main
                        if ($token) {
                            $indent = $statement->indent;
                            $statement->push(new LTactic(
                                'try',
                                new LTactic('echo', $token, $indent),
                                $indent
                            ));
                        }

                        break;
                    }
                }
            }
        }
        return $this;
    }
}


class L_have extends LUnary
{
    public function is_indented()
    {
        return true;
    }
    public function sep()
    {
        $assign = $this->arg;
        if ($assign instanceof LAssign) {
            $lhs = $assign->lhs;
            if ($lhs instanceof LCaret || $lhs instanceof LColon && $lhs->lhs instanceof LCaret)
                return '';
        }
        return ' ';
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

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize()
        ];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
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
        if ($assign instanceof LAssign) {
            $token = $assign->lhs;
            if ($token instanceof LColon)
                $token = $token->lhs;
            if ($token instanceof LCaret)
                $token = new LToken('this', $this->indent);
            if (
                $token instanceof LAngleBracket &&
                $token->arg instanceof LArgsCommaSeparated &&
                std\array_all(fn($arg) => $arg instanceof LToken, $token->arg->args)
            )
                $token = $token->arg;

            if ($token instanceof LToken || $token instanceof LArgsCommaSeparated)
                return $token;
        }
    }

    public function echo()
    {
        $token = $this->get_echo_token();
        if ($token) {
            $by = $this->arg->rhs;
            if ($by instanceof L_by) {
                $stmt = $by->arg;
                if ($stmt instanceof LStatements)
                    $stmt->echo();
            }
            return [
                $this,
                new LTactic('echo', $token, $this->indent)
            ];
        }
        return $this;
    }

    public function split(&$syntax = null)
    {
        $assign = $this->arg;
        if ($assign instanceof LAssign && ($by = $assign->rhs) instanceof L_by && ($stmts = $by->arg) instanceof LStatements) {
            $self = clone $this;
            $self->arg->rhs->arg = new LCaret($by->indent);
            $statements[] = $self;
            foreach ($stmts->args as $stmt)
                array_push($statements, ...$stmt->split($syntax));

            return $statements;
        }
        return [$this];
    }
}

class L_let extends LUnary
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
        //cm-keyword {color: #708;} 
        //defined in static/codemirror/lib/codemirror.css
        return "\\textcolor{#770088}{\\textbf{{$this->command}}}\\ %s";
    }
    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize()
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
        if ($assign instanceof LAssign) {
            $angleBracket = $assign->lhs;
            if ($angleBracket instanceof LAngleBracket) {
                $token = $angleBracket->tokens_comma_separated();
                if (count($token) == 1)
                    return $token[0];
                return new LArgsCommaSeparated($token, $this->indent);
            }
        }
    }
    public function echo()
    {
        $token = $this->get_echo_token();
        if ($token)
            return [
                $this,
                new LTactic('echo', $token, $this->indent)
            ];
        return $this;
    }
}

class L_show extends LSyntax
{
    public function __construct($arg, $indent, $parent = null)
    {
        parent::__construct([$arg], $indent, $parent);
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LStatements || $parent instanceof LArgsNewLineSeparated;
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
            $this->func => parent::jsonSerialize()
        ];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 7;
            default:
                return parent::__get($vname);
        }
    }
}

class L_fun extends LUnary
{
    public static $input_priority = 19;
    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LArgsNewLineSeparated || $parent instanceof LStatements;
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
            $this->func => $this->arg->jsonSerialize()
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

class LbigOperator extends LArgs
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
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function is_indented()
    {
        return $this->parent instanceof LStatements;
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
            $caret = new LCaret($this->indent);
            $this->scope = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


class LQuantifier extends LbigOperator
{
    use LProp;
    public static $input_priority = 24;
    public function latexFormat()
    {
        if (count($this->args) == 1)
            return "$this->command\\ {%s},";
        return "$this->command\\ {%s}, {%s}";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }
}


// universal quantifier
class L_forall extends LQuantifier
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
class L_exists extends LQuantifier
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


class L_sum extends LbigOperator
{
    public static $input_priority = 52;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∑';
            case 'stack_priority':
                return 28;
            default:
                return parent::__get($vname);
        }
    }
}

class L_prod extends LbigOperator
{
    public static $input_priority = 52;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∏';
            case 'stack_priority':
                return 28;
            default:
                return parent::__get($vname);
        }
    }
}

class LLamda extends LbigOperator
{
    public static $input_priority = 52;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'lamda';
            case 'command':
                return 'lamda';
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

function compile($code)
{
    global $tactics;
    $caret = new LCaret(0);
    $root = new LModule([$caret], 0);
    assert(str_ends_with($code, "\n"));
    $tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $code));
    $i = 0;
    $count = count($tokens);
    $tokens[] = ''; // prevent out of bounds error
    $indent = 0;
    while ($i < $count) {
        $token = $tokens[$i];
        switch ($token) {
            case 'import':
            case 'open':
            case 'namespace':
            case 'def':
            case 'theorem':
            case 'lemma':
                $caret = $caret->append("L_$token", "delspec");
                break;
            case 'fun':
            case 'match':
                $caret = $caret->append("L_$token", "expr");
                break;
            case 'have':
            case 'let':
            case 'show':
                $caret = $caret->append("L_$token", "tactic");
                break;

            case 'public':
            case 'private':
            case 'protected':
            case 'noncomputable':
                while ($tokens[++$i] == ' ');
                $caret = $caret->append_accessibility("L_$tokens[$i]", $token);
                break;
            case ' ':
                $caret = $caret->parent->insert_space($caret);
                break;

            case "\t":
                throw new Exception("Tab is not allowed in Lean");
            case "\r":
                error_log("Carriage return is not allowed in Lean");
                break;

            case "\n":
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
                $caret = $caret->parent->insert_newline($caret, $newline_count, $indent, $tokens[$i + $k]);
                $i += $j - 1;
                break;

            case '.':
                if ($caret instanceof LCaret && $caret->parent instanceof LStatements)
                    $caret = $caret->parent->insert_unary($caret, 'LTacticBlock');
                else
                    // $caret instanceof LToken ||
                    // $caret instanceof LPairedGroup ||
                    // $caret instanceof LProperty ||
                    // $caret instanceof LCaret && ($caret->parent instanceof LPairedGroup || $caret->parent instanceof LBar                
                    $caret = $caret->append_binary("LProperty");
                break;

            case 'is':
                if ($caret instanceof LCaret && $caret->parent instanceof LProperty)
                    $caret = $caret->parent->insert_token($caret, $token);
                else {
                    $Type = "L_$token";
                    $not = $i + 2 < $count && std\isspace($tokens[$i + 1]) && strtolower($tokens[$i + 2]) == 'not';
                    if ($not) {
                        $i += 2;
                        $Type .= '_not';
                    }
                    $caret = $caret->append_binary($Type);
                }
                break;

            case '(':
                $caret = $caret->parent->insert_left($caret, 'LParenthesis');
                break;

            case ')':
                $caret = $caret->parent->append_right('LParenthesis');
                break;

            case '[':
                $caret = $caret->parent->insert_left($caret, 'LBracket', $i ? $tokens[$i - 1] : '');
                break;

            case ']':
                $caret = $caret->parent->append_right('LBracket');
                break;

            case '{':
                $caret = $caret->parent->insert_left($caret, 'LBrace');
                break;

            case '}':
                $caret = $caret->parent->append_right('LBrace');
                break;

            case '⟨':
                $caret = $caret->parent->insert_left($caret, 'LAngleBracket');
                break;
            case '⟩':
                $caret = $caret->parent->append_right('LAngleBracket');
                break;

            case '⌈':
                $caret = $caret->parent->insert_left($caret, 'LCeil');
                break;
            case '⌉':
                $caret = $caret->parent->append_right('LCeil');
                break;

            case '⌊':
                $caret = $caret->parent->insert_left($caret, 'LFloor');
                break;
            case '⌋':
                $caret = $caret->parent->append_right('LFloor');
                break;

            case '«':
                $caret = $caret->parent->insert_left($caret, 'LDoubleAngleQuotation');
                break;
            case '»':
                $caret = $caret->parent->append_right('LDoubleAngleQuotation');
                break;
            case '?':
                if ($caret instanceof LGetElem) {
                    $parent = $caret->parent;
                    [$lhs, $rhs] = $caret->args;
                    $new = new LGetElemQue($lhs, $rhs, $caret->indent);
                    $parent->replace($caret, $new);
                    $caret = $new;
                }
                else {
                    if ($tokens[$i + 1] == '_') {
                        ++$i;
                        $token .= '_';
                    }
                    $caret = $caret->parent->insert_token($caret, $token);
                }
                break;
            case '<':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    $caret = $caret->append_binary('L_le');
                } elseif ($i + 2 < $count && $tokens[$i + 1] == ';' && $tokens[$i + 2] == '>') {
                    $i += 2;
                    $caret = $caret->parent->insert_sequential_tactic_combinator($caret);
                } else
                    $caret = $caret->append_binary('L_lt');
                break;

            case '>':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    $caret = $caret->append_binary('L_ge');
                } else
                    $caret = $caret->append_binary('L_gt');
                break;

            case '≤':
                $caret = $caret->append_binary('L_le');
                break;

            case '≥':
                $caret = $caret->append_binary('L_ge');
                break;

            case '=':
                if ($tokens[$i + 1] == '>') {
                    ++$i;
                    $caret = $caret->append_binary('LRightarrow');
                } else
                    $caret = $caret->append_binary('LEq');
                break;

            case '!':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    $caret = $caret->append_binary('L_ne');
                } else
                    throw new Exception("Unexpected token $token");
                break;

            case '≠':
                $caret = $caret->append_binary('L_ne');
                break;

            case '≡':
                $caret = $caret->append_binary('L_equiv');
                break;

            case '≢':
                $caret = $caret->append_binary('LNotEquiv');
                break;

            case ',':
                $caret = $caret->parent->insert_comma($caret);
                break;

            case ':':
                if ($tokens[$i + 1] == '=') {
                    ++$i;
                    $caret = $caret->parent->insert_assign($caret);
                } elseif ($tokens[$i + 1] == ':') {
                    ++$i;
                    if ($tokens[$i + 1] == 'ᵥ') {
                        ++$i;
                        $caret = $caret->parent->insert_vconstruct($caret);
                    } else
                        $caret = $caret->parent->insert_construct($caret);
                } else
                    $caret = $caret->parent->insert_colon($caret);
                break;

            case ';':
                $caret = $caret->parent->append_semicolon();
                break;

            case '-':
                if ($tokens[$i + 1] == '-') {
                    ++$i;
                    $comment = "";
                    while ($tokens[++$i] != "\n")
                        $comment .= $tokens[$i];
                    $caret = $caret->parent->insert_line_comment($caret, trim($comment));
                    --$i; // now $tokens[++$i] must be a new line;
                } elseif ($caret instanceof LCaret)
                    $caret = $caret->parent->insert_unary($caret, 'LNeg');
                else
                    $caret = $caret->append_arithmetic($token);
                break;

            case '*':
                if ($caret instanceof LCaret)
                    $caret = $caret->parent->insert_token($caret, $token);
                else
                    $caret = $caret->append_arithmetic($token);
                break;

            case '|':
                $next_token = $tokens[$i + 1];
                if ($next_token == '|') {
                    ++$i;
                    $caret = $caret->parent->append_arithmetic('||');
                } elseif ($next_token == '>') {
                    ++$i;
                    if ($tokens[$i + 1] == '.') {
                        ++$i;
                        $caret = $caret->append_arithmetic('|>.');
                    } else
                        $caret = $caret->append_post_unary('LPipeForward');
                } else
                    $caret = $caret->parent->insert_bar($caret, $tokens[$i - 1], $next_token);
                break;

            case '&':
                if ($tokens[$i + 1] == '&') {
                    $caret = $caret->parent->append_arithmetic('&&');
                    ++$i;
                } else
                    $caret = $caret->parent->insert_bitand($caret);
                break;

            case "'":
                while (preg_match("/['\w]/", $tokens[$i + 1]))
                    $token .= $tokens[++$i];
                $caret = $caret->append_quote($token);
                break;

            case '+':
                if ($caret instanceof LCaret)
                    $caret = $caret->parent->insert_unary($caret, 'LPlus');
                else {
                    if ($tokens[$i + 1] == '+') {
                        ++$i;
                        $token .= '+';
                    }
                    $caret = $caret->append_arithmetic($token);
                }
                break;
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
                    $caret = $caret->append_block_comment($comment, $docstring);
                    if ($tokens[$i + 1] == "\n")
                        ++$i;
                    break;
                }

                if ($tokens[$i + 1] == '/') {
                    $caret = $caret->append_arithmetic('//');
                    ++$i;
                    break;
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
                $caret = $caret->append_arithmetic($token);
                break;

            case '←':
                $caret = $caret->parent->insert_unary($caret, 'L_leftarrow');
                break;

            case '→':
                $caret = $caret->append_binary('L_rightarrow');
                break;

            case '↦':
                $caret = $caret->append_binary('L_mapsto');
                break;

            case '↔':
                $caret = $caret->append_binary('L_leftrightarrow');
                break;

            case '∀':
                $caret = $caret->append('L_forall', 'operator');
                break;

            case '∃':
                $caret = $caret->append('L_exists', 'operator');
                break;

            case '∑':
                $caret = $caret->append('L_sum', 'operator');
                break;

            case '∏':
                $caret = $caret->append('L_prod', 'operator');
                break;

            case '∧':
                $caret = $caret->append_binary('L_land');
                break;

            case '∨':
                $caret = $caret->append_binary('L_lor');
                break;

            case '⊆':
                $caret = $caret->append_binary('L_subseteq');
                break;

            case '⊇':
                $caret = $caret->append_binary('L_supseteq');
                break;

            case '¬':
                $caret = $caret->parent->insert_unary($caret, 'L_lnot');
                break;

            case '√':
                $caret = $caret->parent->insert_unary($caret, 'L_sqrt');
                break;

            case '∛':
                $caret = $caret->parent->insert_unary($caret, 'LCubicRoot');
                break;

            case '∜':
                $caret = $caret->parent->insert_unary($caret, 'LQuarticRoot');
                break;

            case '↑':
                $caret = $caret->parent->insert_unary($caret, 'L_uparrow');
                break;

            case '²':
                $caret = $caret->append_post_unary('LSquare');
                break;

            case '³':
                $caret = $caret->append_post_unary('LCube');
                break;

            case '⁴':
                $caret = $caret->append_post_unary('LTesseract');
                break;

            case '⁻':
                if ($tokens[$i + 1] == '¹') {
                    ++$i;
                    $caret = $caret->append_post_unary('LInv');
                }
                break;

            case 'by':
            case 'calc':
                # modifiers
            case 'using':
            case 'at':
            case 'with':
            case 'in':
            case 'generalizing':
            case 'MOD':
            case 'from':
                $caret = $caret->parent->insert($caret, "L_$token", "modifier");
                break;

            case '·':
                if ($caret->parent instanceof LStatements || $caret->parent instanceof LSequentialTacticCombinator)
                    $caret = $caret->parent->insert_unary($caret, 'LTacticBlock');
                else
                    //Middle Dot token
                    $caret = $caret->parent->insert_token($caret, $token);
                break;

            case '@':
                $caret = $caret->parent->insert_unary($caret, 'LAttribute');
                break;

            case 'end':
                $caret = $caret->parent->insert_end($caret);
                break;

            case 'only':
                $caret = $caret->parent->insert_only($caret);
                break;

            case 'if':
                $caret = $caret->parent->insert_if($caret);
                break;

            case 'then':
                $caret = $caret->parent->insert_then($caret);
                break;

            case 'else':
                $caret = $caret->parent->insert_else($caret);
                break;

            case '‖':
                if ($caret instanceof LCaret || $tokens[$i - 1] == ' ')
                    $caret = $caret->parent->insert_left($caret, 'LNorm');
                else
                    $caret = $caret->parent->append_right('LNorm');
                break;

            default:
                $token_orig = $token;
                $index = std\binary_search($tactics, $token_orig, "strcmp");
                $next_char = $tokens[$i + 1];
                if ($next_char == "'" || $next_char == "!" || $next_char == "?") {
                    ++$i;
                    $token .= $next_char;
                }
                if ($index < count($tactics) && $tactics[$index] == $token_orig)
                    $caret = $caret->parent->insert_tactic($caret, $token);
                else
                    $caret = $caret->parent->insert_token($caret, $token);
        }
        if (!$caret)
            break;
        ++$i;
    }

    return $root;
}

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
    // SetEnv USERPROFILE "C:\Users\admin"
    // Configure Git environment variables to trust the directory
    $cwd = getcwd();
    $repository = scandir("$cwd/.lake/packages");
    $repository = array_slice($repository, 2); // Remove . and ..
    $env = [
        'GIT_CONFIG_COUNT' => count($repository),
        // Preserve other important environment variables
        'PATH' => getenv('PATH'),
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
