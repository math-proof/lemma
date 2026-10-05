<?php
/**
 * Indexing (`LeanGetElem`, `LeanGetElemQue`, `LeanGetElemQuote`).
 *
 * Loaded by lean.php after the `LeanGetElemBase` traits. JS also has
 * `LeanGetWhiteSquareBracket`; this file does not.
 * Mirrors static/js/parser/lean/indexing.js. Not a standalone entry point.
 */

class LeanGetElem extends LeanBinary
{
    public static $input_priority = 67;
    use LeanGetElemBaseBinary;

    public function collectGetElemChain()
    {
        $indices = [];
        $node = $this;
        while ($node instanceof LeanGetElem) {
            array_unshift($indices, $node->rhs);
            $node = $node->lhs;
        }
        return ['base' => $node, 'indices' => $indices];
    }

    public function latexArgs(&$syntax = null)
    {
        // Nested segment of a longer chain: outer node owns multi-index LaTeX.
        if ($this->parent instanceof LeanGetElem)
            return parent::latexArgs($syntax);

        ['base' => $base, 'indices' => $indices] = $this->collectGetElemChain();
        $indexParts = array_map(fn($ix) => $ix->toLatex($syntax), $indices);
        $indexLatex = implode(', ', $indexParts);

        if ($base instanceof LeanProperty && $base->rhs instanceof LeanToken) {
            $fmt = $base->latexFormat();
            $args = $base->latexArgs($syntax);
            if ($args && str_contains($fmt, '%s')) {
                $args[0] = '{' . $base->lhs->toLatex($syntax) . '}_{' . $indexLatex . '}';
                return $args;
            }
        }

        if (count($indices) >= 2)
            return array_merge([$base->toLatex($syntax)], $indexParts);

        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        if ($this->parent instanceof LeanGetElem)
            return '{%s}_{%s}';

        ['base' => $base, 'indices' => $indices] = $this->collectGetElemChain();
        if ($base instanceof LeanProperty && $base->rhs instanceof LeanToken) {
            $fmt = $base->latexFormat();
            if (str_contains($fmt, '%s'))
                return $fmt;
        }
        if (count($indices) >= 2)
            return '{%s}_{' . implode(', ', array_fill(0, count($indices), '%s')) . '}';

        return '{%s}_{%s}';
    }

    public function strFormat()
    {
        return '%s[%s]';
    }
}

class LeanGetElemQue extends LeanBinary
{
    public static $input_priority = 67;
    use LeanGetElemBaseBinary;
    public function latexFormat()
    {
        return '{%s}_{%s?}';
    }
    public function strFormat()
    {
        return '%s[%s]?';
    }
}

class LeanGetElemQuote extends LeanArgs
{
    public static $input_priority = 67;
    use LeanGetElemBase;
    public function latexFormat()
    {
        return "{%s}_{%s{\\color{red}\\text{'}}%s}";
    }
    public function strFormat()
    {
        return "%s[%s]'%s";
    }
}

// END OF indexing family (Lean_is stays in lean.php)
