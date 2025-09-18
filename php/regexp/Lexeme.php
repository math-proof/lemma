<?php
require_once __DIR__.'/../parser/regexp.php';

class Lexeme
{

    public $regex;

    public function match_length() {
        return $this->regex->match_length();
    }

    public function is_or_structure()
    {
        return $this->regex->is_or_structure();
    }

    public function is_possibly_empty()
    {
        return $this->regex->is_possibly_empty();
    }

    public function has_group_captured()
    {
        return $this->regex->has_group_captured();
    }

    public function __construct($regex)
    {
        $this->regex = $regex;
    }

    public static function construct($s)
    {
        $s = preg_replace_callback("/(?<![\\\\])\[\^((?:[^\[\]\{\}]|(?<=[\\\\])[\[\]])*)(?<![\\\\])\]/", fn(&$m) => "[^$m[1]{}]", $s);
        
        $s = preg_replace_callback("/\\\\([DWS])/", fn(&$m) => "[^\\".strtolower($m[1])."{}]", $s);

        $regex = Regex::compile($s)->arg;
        $negate = $regex->remove_negation();
        if ($regex->is_or_structure())
            return $negate ? new LexemeComplexNegate($regex) : new LexemeComplex($regex);
        else
            return $negate ? new LexemeSimpleNegate($regex) : new LexemeSimple($regex);
    }

    public function regexp($braceIsPrefixed, $beginIsConsumed, $projective = true)
    {
        if ($projective) {
            if ($this->has_group_captured()) {
                if ($this->is_or_structure())
                    $word = "(?:$this)";
                else
                    $word = "$this";
            } else
                $word = "($this)";

            if ($braceIsPrefixed)
                return $word;

            if ($beginIsConsumed) {
                if ($this->match_length() === 0) {
                    return $word;
                }
                return "(?<=[{}])$word";
            }

            return "(?<=[{}]|^)$word";
        } else {
            $word = "$this";
            $word .= "(?: \\d+)?";

            if ($this->has_group_captured())
                $word = "(?:${word})";
            else
                $word = "(${word})";

            if ($braceIsPrefixed)
                return $word;

            if ($beginIsConsumed) {
                if ($this->match_length() === 0) {
                    return $word;
                }
                return "(?<=[{}])$word";
            }

            return "(?<=[{}]|^)${word}";
        }
    }
}

class LexemeSimple extends Lexeme
{

    public function __toString()
    {
        return "$this->regex";
    }
}

class LexemeSimpleNegate extends Lexeme
{

    public function __toString()
    {
        $regex = $this->regex;
        if ($regex instanceof RegexGroupCaptured) {
            return "(?!$regex->arg)([^{}]+)";
        }
        else{
            return "(?!$regex)[^{}]+";
        }
    }
}

class LexemeComplex extends Lexeme
{

    // return true if the given word matches any one of the pattern
    public function __toString()
    {
        return "(?:$this->regex)";
    }

    public function regexp($braceIsPrefixed, $beginIsConsumed, $projective = true)
    {
        $groupIsExistent = $this->has_group_captured();

        if ($projective) {
            $word = "($this)";
        } else {
            $word = "$this";
            $word .= "(?: \\d+)?";

            if ($groupIsExistent)
                $word = "(?:${word})";
            else
                $word = "(${word})";
        }

        if ($braceIsPrefixed)
            return $word;

        if ($beginIsConsumed) {
            if ($this->match_length() === 0) {
                return $word;
            }
            return "(?<=[{}])$word";
        }

        return "(?<=[{}]|^)${word}";
    }
}

class LexemeComplexNegate extends Lexeme
{

    /*
     * return true if the given word does not match any one of the pattern
     */
    public function __toString()
    {
        return "(?!(?:$this->regex))[^{}]+";
    }
}
?>