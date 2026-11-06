<?php
/**
 * Quantifiers (`LeanQuantifier`, ∀, ∃).
 *
 * Loaded by lean.php after `bigops.php` (`LeanQuantifier` extends `LeanBigOperator`).
 * Mirrors js/parser/lean/quantifier.js. Not a standalone entry point.
 */

class LeanQuantifier extends LeanBigOperator
{
    use LeanProp;
    public function holeRegexTag()
    {
        return null;
    }

    public function holeRegex($opts = [])
    {
        $tag = $this->holeRegexTag();
        if (!$tag) return parent::holeRegex($opts);
        $bodyNode = $this->scope ?? ($this->args[count($this->args) - 1] ?? null);
        if ($tag === "All" && isset($opts["peelGuards"]) && is_callable($opts["peelGuards"]))
            $bodyNode = $opts["peelGuards"]($bodyNode);
        $body = $bodyNode ? $bodyNode->holeRegex($opts) : null;
        if ($body === null || $body === "") return $tag;
        if ($body === $tag || str_starts_with($body, $tag . "_")) return $body;
        return $tag . "_" . wrapHoleOpt($body);
    }

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

    public function holeRegexTag()
    {
        return "All";
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

    public function holeRegexTag()
    {
        return "Any";
    }

}

// END OF quantifier family
