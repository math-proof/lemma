<?php
/**
 * Arithmetic operator family (add/sub/mul/div/pow, matmul, bit ops, modular,
 * append, and the unary helpers that only serve them).
 *
 * Loaded by lean.php after LeanBinary and LeanUnary are declared.
 * Mirrors static/js/parser/lean/arithmetic.js. Not a standalone entry point.
 */

abstract class LeanArithmetic extends LeanBinary
{
    public static $input_priority = 67;
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret instanceof LeanCaret)
            return $caret;
        return $this->parent->insert_newline($this, $newline_count, $indent, $next);
    }
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

    public function latexArgs(&$syntax = null)
    {
        [$lhs, $rhs] = $this->args;
        $level = $this->level;
        if ($rhs instanceof LeanParenthesis && $rhs->arg instanceof LeanDiv) {
            // if $rhs->arg instanceof LeanPow, the parenthesis is unnecessary
            $rhs = $rhs->arg;
        } elseif ($rhs instanceof LeanNeg) {
            $rhs = new LeanParenthesis($rhs, $this->indent, $level);
            $rhs->is_closed = true;
        } 

        if ($lhs instanceof LeanParenthesis && $lhs->arg instanceof LeanDiv) {
            $lhs = $lhs->arg;
        } elseif ($lhs instanceof LeanNeg) {
            $lhs = new LeanParenthesis($lhs, $this->indent, $level);
            $lhs->is_closed = true;
        }
        $lhs = $lhs->toLatex($syntax);
        $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
    public function latexFormat()
    {
        return "%s $this->command %s";
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

    public function isMatMulContext()
    {
        return true;
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

    public function latexArgs(&$syntax = null)
    {
        $lhs = $this->lhs->peelLatexCoe();
        $rhs = $this->rhs->peelLatexCoe();
        if ($lhs instanceof LeanDiv) {
        } else {
            if ($lhs instanceof LeanParenthesis && !($lhs->arg instanceof LeanColon))
                $lhs = $lhs->arg;
            if ($rhs instanceof LeanParenthesis && !($rhs->arg instanceof LeanColon))
                $rhs = $rhs->arg;
        }
        $lhs = $lhs->toLatex($syntax);
        if ($rhs instanceof LeanDiv)
            $rhs = sprintf('\left. {%s} \right/ {%s}', ...$rhs->latexArgs($syntax));
        else
            $rhs = $rhs->toLatex($syntax);
        return [$lhs, $rhs];
    }
    public function latexFormat()
    {
        if ($this->lhs instanceof LeanDiv) {
            return '\left. {%s} \right/ {%s}';
        }
        return '\frac {%s} {%s}';
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

class LeanBitwiseAnd extends LeanArithmetic
{
    public static $input_priority = 60;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\\&\!\!\\&\!\!\\&';
            case 'operator':
                return '&&&';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanBitwiseXor extends LeanArithmetic
{
    public static $input_priority = 60;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '\^\^\^';
            case 'operator':
                return '^^^';
            default:
                return parent::__get($vname);
        }
    }
}

class LeanBitOr extends LeanArithmetic
{
    // used in the syntax:
    // rcases lt_trichotomy 0 a with ha | h_0 | ha
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

    public function insert_bar($caret, $prev_token, $next)
    {
        if ($caret instanceof LeanToken) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->replace($caret, new LeanBitOr($caret, $new, $this->indent, $caret->level));
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return false;
    }

    public function latexArgs(&$syntax = null)
    {
        if ($this->parent instanceof LeanQuantifier)
            $syntax['setOf'] = true;
        return parent::latexArgs($syntax);
    }
    public function tokens_bar_separated()
    {
        $tokens = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof LeanBitOr)
                $tokens = [...$tokens, ...$arg->tokens_bar_separated()];
            elseif ($arg instanceof LeanAngleBracket) {
                $ts = $arg->tokens_comma_separated();
                $tokens[] = count($ts) === 1 ? $ts[0] : new LeanArgsCommaSeparated($ts, $this->indent, $this->level);
            }
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
                ), $indent, 0);
            else {
                $token = clone $token;
                $token->indent = $indent;
            }
            return $token;
        }
    }

}

class LeanBitwiseOr extends LeanArithmetic
{
    public static $input_priority = 55;

    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
            case 'operator':
                return '|||';
            default:
                return parent::__get($vname);
        }
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
        $lhs = $lhs->peelLatexCoe();
        $rhs = $rhs->peelLatexCoe();
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

class Lean_lll extends LeanArithmetic
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '<<<';
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

class Lean_ggg extends LeanArithmetic
{
    public static $input_priority = 75;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '>>>';
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

    public function flattenAppend()
    {
        return array_merge($this->lhs->flattenAppend(), $this->rhs->flattenAppend());
    }

    public function latexArgs(&$syntax = null)
    {
        $args = $this->matrixLatexArgs($syntax);
        if ($args !== null)
            return $args;
        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        $rows = $this->matrixLatexSpec();
        if ($rows)
            return self::bmatrixFormat(count($rows), count($rows[0]));
        return parent::latexFormat();
    }

    public static function bmatrixFormat($nrows, $ncols)
    {
        $row = implode(' & ', array_fill(0, $ncols, '%s'));
        return '\\begin{bmatrix} ' . implode(' \\\\ ', array_fill(0, $nrows, $row)) . ' \\end{bmatrix}';
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

    public function latexFormat()
    {
        return "$this->command{%s}";
    }
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

}

class LeanPlus extends LeanUnaryArithmeticPre
{
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
    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }
}

class LeanInv extends LeanUnaryArithmeticPost
{
    public static $input_priority = 1024;
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
    public function latexArgs(&$syntax = null)
    {
        return [$this->arg->peelLatexCoe()->toLatex($syntax)];
    }
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }
}

class LeanFactorial extends LeanUnaryArithmeticPost
{
    public static $input_priority = 10000;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return '!';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '{%s}!';
    }
    public function strFormat()
    {
        return '%s !';
    }
}

class LeanPosPart extends LeanUnaryArithmeticPost
{
    public static $input_priority = 71;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⁺';
            case 'command':
                return '^{+}';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }
}

class LeanNegPart extends LeanUnaryArithmeticPost
{
    public static $input_priority = 71;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '⁻';
            case 'command':
                return '^{-}';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }
}

class Lean_partial extends LeanUnaryArithmeticPre
{
    public static $input_priority = 75;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '∂';
            default:
                return parent::__get($vname);
        }
    }
}

class Lean_sqrt extends LeanUnaryArithmeticPre
{
    public static $input_priority = 72;
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
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg->peelLatexCoe();
        if ($arg instanceof LeanParenthesis)
            $arg = $arg->arg;
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }
    public function strFormat()
    {
        return "$this->operator%s";
    }

}

class LeanConj extends LeanUnaryArithmeticPre
{
    public static $input_priority = 1024;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return '~';
            case 'command':
                return '\\overline';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return '\\overline{%s}';
    }
    public function strFormat()
    {
        return "$this->operator%s";
    }
}

class LeanSquare extends LeanUnaryArithmeticPost
{
    public static $input_priority = 66; //LeanAdd::$input_priority + 1;
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

    public function latexFormat()
    {
        return "{%s}$this->command";
    }
    public function strFormat()
    {
        return "%s$this->operator";
    }

}

class LeanCubicRoot extends LeanUnaryArithmeticPre
{
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
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis)
            $arg = $arg->arg;
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }
}

class Lean_uparrow extends LeanUnaryArithmeticPre
{
    public static $input_priority = 1024;
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
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis && $arg->arg instanceof LeanArgsSpaceSeparated && $arg->arg->is_Abs())
            $arg = $arg->arg;
        return [$arg->toLatex($syntax)];
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function peelLatexCoe()
    {
        return $this->arg->peelLatexCoe();
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

}

class LeanUparrow extends LeanUnaryArithmeticPre
{
    public static $input_priority = 1024;
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
    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

}

class LeanCube extends LeanUnaryArithmeticPost
{
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
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }

}

class LeanQuarticRoot extends LeanUnaryArithmeticPre
{
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
    public function latexArgs(&$syntax = null)
    {
        $arg = $this->arg;
        if ($arg instanceof LeanParenthesis)
            $arg = $arg->arg;
        $arg = $arg->toLatex($syntax);
        return [$arg];
    }

    public function latexFormat()
    {
        return "$this->command{%s}";
    }

    public function strFormat()
    {
        return "$this->operator%s";
    }

}

class LeanTesseract extends LeanUnaryArithmeticPost
{
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
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }

}

class LeanTranspose extends LeanUnaryArithmeticPost
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'ᵀ';
            case 'command':
                return '^\top';
            default:
                return parent::__get($vname);
        }
    }
    public function latexFormat()
    {
        return "{%s}$this->command";
    }

    public function strFormat()
    {
        return "%s$this->operator";
    }

}

class LeanPipeForward extends LeanUnaryArithmeticPost
{
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
    public function latexFormat()
    {
        return "{%s} $this->command";
    }

    public function strFormat()
    {
        return "%s $this->operator";
    }

}

// END OF arithmetic family (LeanCommand stays in lean.php)
