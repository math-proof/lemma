<?php
/**
 * Quantifiers (`LeanQuantifier`, ∀, ∃).
 *
 * Loaded by lean.php after LeanBigOperator. ∑ / ∏ / ∫ stay in lean.php.
 * Mirrors static/js/parser/lean/quantifier.js. Not a standalone entry point.
 */

class LeanQuantifier extends LeanBigOperator
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

// END OF quantifier family
