<?php
/**
 * Field access `a.b` (`LeanProperty`).
 *
 * Loaded by lean.php after `range.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/property.js. Not a standalone entry point.
 */

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

// END OF property family (LeanStatements stays in lean.php)
