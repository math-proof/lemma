<?php
/**
 * Leaf Lean nodes (`LeanCaret`, `LeanToken`, line/block comments, doc strings).
 *
 * Loaded by lean.php after `base.php` and before `LeanArgs`. Mirrors
 * static/js/parser/lean/atomic.js. The empty binary token classes are JS-only.
 * Not a standalone entry point.
 */

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

// END OF atomic family (LeanCommand stays in lean.php)
