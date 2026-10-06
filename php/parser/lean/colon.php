<?php
/**
 * Type ascription and declaration colon (`LeanColon`, `a : T`).
 *
 * Loaded by lean.php after `property.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/colon.js. PHP `insert_newline` and
 * `strFormat` stay shorter than the JS methods. Not a standalone entry point.
 */

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

    /** `(h : P) : -- note`, held until insert_newline opens the statements block (mirrors colon.js). */
    public $pendingComment = null;

    public function insert_line_comment($caret, $comment)
    {
        if ($caret instanceof LeanCaret && $this->rhs === $caret && $this->pendingComment === null) {
            $this->pendingComment = $comment;
            return $caret;
        }
        return parent::insert_line_comment($caret, $comment);
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        $pendingComment = $this->pendingComment;
        $this->pendingComment = null;
        if ($this->rhs === $caret) {
            if ($caret instanceof LeanCaret && $indent > $this->indent) {
                $caret->indent = $indent;
                $stmts = new LeanStatements([$caret], $indent, $caret->level);
                if ($pendingComment !== null)
                    $stmts->unshift(new LeanLineComment($pendingComment, $indent, $caret->level));
                $this->rhs = $stmts;
                return $caret;
            }
            if ($caret instanceof LeanStatements && $indent == $this->indent && $this->parent instanceof LeanParenthesis)
                return $caret;
        }
        if ($pendingComment !== null && $this->rhs === $caret)
            $caret = $caret->push_line_comment($pendingComment);
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

// END OF colon family (LeanParser stays in lean.php)
