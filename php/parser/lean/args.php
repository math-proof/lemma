<?php
/**
 * Argument lists (space, newline, indented, comma, semicolon, comma-newline).
 *
 * Loaded by lean.php after `ite.php`. Extends `LeanArgs` / `LeanBinary`, which
 * already exist. Mirrors static/js/parser/lean/args.js. Not a standalone entry point.
 */

class LeanArgsSpaceSeparated extends LeanArgs
{
    public static $input_priority = 80; // exp x ^ n where exp x evaluates first
    public $cache = null;
    public function construct_prefix_tree() {
        $tokens = $this->tokens_space_separated();
        $tree = std\eval_prefix($tokens, fn($arg) => $arg->operand_count());
        return $tree;
    }

    public function peelGroup()
    {
        return count($this->args) === 1 ? $this->args[0]->peelGroup() : $this;
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

    public function hstackBlocks()
    {
        $func = $this->args[0];
        if (!($func instanceof LeanProperty) || !($func->rhs instanceof LeanToken) || $func->rhs->text !== 'hstack')
            return null;
        $n = count($this->args);
        if ($n === 2)
            return [$func->lhs, $this->args[1]];
        if ($n === 3)
            return [$this->args[1], $this->args[2]];
        return null;
    }

    public function insert($caret, $func, $type)
    {
        if ($caret === end($this->args) && !$caret instanceof LeanCaret && $type != 'modifier') {
            $caret = new LeanCaret($this->indent, $caret->level);
            $this->push(new $func($caret, $caret->indent, $caret->level));
            return $caret;
        } elseif ($this->parent)
            return $this->parent->insert($this, $func, $type);
    }

    public function insert_colon($caret)
    {
        for ($n = $caret; $n !== null && $n->parent !== null; $n = $n->parent) {
            $p = $n->parent;
            if ($p instanceof LeanIte && $p->if === $n) {
                $c = new LeanCaret($caret->indent, $caret->level);
                $caret->parent->replace($caret, new LeanColon($caret, $c, $caret->indent, $caret->level));
                return $c;
            }
        }
        return $caret->push_binary('LeanColon');
    }

    public function insert_unary($caret, $func)
    {
        if ($caret === end($this->args)) {
            $indent = $this->indent;
            if ($caret instanceof LeanCaret) {
                $new = new $func($caret, $indent, $caret->level);
                $this->replace($caret, $new);
            } else {
                $caret = new LeanCaret($indent, $caret->level);
                $new = new $func($caret, $indent, $this->level);
                $this->push($new);
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_word($caret, $word)
    {
        $new = new LeanToken($word, $this->indent, $caret->level);
        $this->push($new);
        return $new;
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

    public function is_MatProd()
    {
        $args = $this->args;
        if (count($args) !== 3)
            return false;
        $func = $args[0];
        $isMatProd =
            ($func instanceof LeanToken && $func->text === 'matProd') ||
            ($func instanceof LeanProperty &&
                $func->rhs instanceof LeanToken &&
                $func->rhs->text === 'matProd');
        if (!$isMatProd)
            return false;
        $peel = fn($arg) => $arg instanceof LeanParenthesis ? $arg->arg : $arg;
        $fn = $peel($args[2]);
        if (!($fn instanceof Lean_fun))
            return false;
        $arrow = $fn->arg;
        return $arrow instanceof LeanRightarrow || $arrow instanceof Lean_mapsto;
    }

    /**
     * LaTeX parts for matProd: `[i, n, body]` for `\prod\limits_{i < n} {body}`.
     * @return array{0: string, 1: string, 2: string}|null
     */
    public function matProdLatexParts(&$syntax = null)
    {
        if (!$this->is_MatProd())
            return null;
        $peel = fn($arg) => $arg instanceof LeanParenthesis ? $arg->arg : $arg;
        $n = $peel($this->args[1]);
        $arrow = $peel($this->args[2])->arg;
        $binder = $peel($arrow->lhs);
        if ($binder instanceof LeanColon)
            $binder = $binder->lhs;
        return [$binder->toLatex($syntax), $n->toLatex($syntax), $arrow->rhs->toLatex($syntax)];
    }

    public function is_Expectation()
    {
        $args = $this->args;
        return count($args) === 3
            && $args[0] instanceof LeanToken
            && $args[0]->text === 'Expectation';
    }

    /**
     * LaTeX parts for `Expectation ν f` — the expectation of `f` under the law `ν`.
     * The two common laws are pretty-printed sympy-style (nodes keep their own
     * rv-coloring):
     *   `Expectation (𝕡.map x) f` → 𝔼(f(x))
     *   `Expectation (ReferenceMeasure.measure.withDensity (fun a ↦ 𝕡.condProb (x, y) (a, b))) f`
     *                             → 𝔼(f(x) | y = b)
     * otherwise the law is shown as the subscript: 𝔼_ν(f).
     * @return array [kind, ...nodes] or null if not an Expectation application
     */
    public function expectationLatexParts()
    {
        if (!$this->is_Expectation())
            return null;
        $peel = fn($arg) => $arg instanceof LeanParenthesis ? $arg->arg : $arg;
        $f = $this->args[2];
        $nu = $peel($this->args[1]);
        if ($nu instanceof LeanArgsSpaceSeparated && count($nu->args) === 2) {
            $head = $nu->args[0];
            $arg = $nu->args[1];
            $isProperty = $head instanceof LeanProperty && $head->rhs instanceof LeanToken;
            if ($isProperty && $head->rhs->text === 'map')
                return ['map', $f, $arg];
            if ($isProperty && $head->rhs->text === 'withDensity'
                && ($fn = $peel($arg)) instanceof Lean_fun) {
                $arrow = $fn->arg;
                $body = $arrow->rhs->peelGroup();
                if ($body instanceof LeanArgsSpaceSeparated && count($body->args) === 3
                    && ($cd = $body->args[0]) instanceof LeanProperty
                    && $cd->rhs instanceof LeanToken && $cd->rhs->text === 'condProb'
                    && ($joint = $body->args[1]->peelGroup()) instanceof LeanArgsCommaSeparated
                    && count($joint->args) === 2
                    && ($val = $body->args[2]->peelGroup()) instanceof LeanArgsCommaSeparated
                    && count($val->args) === 2
                    && trim((string)$val->args[0]) === trim((string)$arrow->lhs->peelGroup()))
                    return ['cond', $f, $joint->args[0], $joint->args[1], $val->args[1]];
            }
        }
        return ['generic', $f, $nu];
    }

    /** Format for expectationLatexParts(). */
    public function expectationLatexFormat(array $parts)
    {
        switch ($parts[0]) {
            case 'map':
                return '\mathop{\mathbb{E}}\left(%s\left(%s\right)\right)';
            case 'cond':
                return '\mathop{\mathbb{E}}\left(%s\left(%s\right)\ \mathrel{\bigg|}\ %s = %s\right)';
            default:
                return '\mathop{\mathbb{E}}\limits_{%s}\left(%s\right)';
        }
    }

    /** An explicit named-implicit argument `(name := value)`, as in `eye (α := α) m`. */
    public function is_named_implicit_arg($arg) : bool
    {
        if ($arg instanceof LeanParenthesis)
            $arg = $arg->arg;
        return $arg instanceof LeanAssign && $arg->lhs instanceof LeanToken;
    }

    /**
     * The single positional argument of `eye n` / `Tensor.eye n`, ignoring explicit
     * named-implicit args such as `(α := α)`; null for any other function or arity.
     * @return array|null
     */
    public function eye_positional_args(array $args)
    {
        $func = $args[0] ?? null;
        $isEye =
            ($func instanceof LeanToken && $func->text === 'eye') ||
            ($func instanceof LeanProperty &&
                $func->rhs instanceof LeanToken &&
                $func->rhs->text === 'eye');
        if (!$isEye)
            return null;
        $positional = array_values(array_filter(
            array_slice($args, 1),
            fn($arg) => !$this->is_named_implicit_arg($arg)
        ));
        return count($positional) === 1 ? $positional : null;
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements ||
            $parent instanceof LeanArgsCommaNewLineSeparated ||
            $parent instanceof LeanArgsNewLineSeparated ||
            $parent instanceof LeanIte && ($this === $parent->then || $this === $parent->else);
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
                case 'Infinitesimal':
                case 'Infinite':
                case 'InfinitePos':
                case 'InfiniteNeg':
                    return true;
            }
        }
    }

    public function is_space_separated()
    {
        return true;
    }

    /** `id (α := T) e` — identity; LaTeX prints only `e`. */
    public function idLatexInner()
    {
        $args = $this->args;
        if (count($args) !== 3 || !($args[0] instanceof LeanToken) || $args[0]->text !== 'id')
            return null;
        $named = $args[1] instanceof LeanParenthesis ? $args[1]->arg : $args[1];
        if (!($named instanceof LeanAssign && $named->lhs instanceof LeanToken && $named->lhs->text === 'α'))
            return null;
        $inner = $args[2];
        if (
            $inner instanceof LeanParenthesis &&
            !($inner->arg instanceof LeanColon) &&
            $this->canStripIdParen($inner->arg)
        )
            $inner = $inner->arg;
        return $inner;
    }

    /** Strip `(e)` after dropping `id` when `e` binds tighter than `id`'s parent. */
    /**
     * `A op B op' C` compares `op.stack_priority` with `op'.input_priority`.
     * After dropping `id`, `inner` is `op` on the left and `op'` on the right.
     */
    public function canStripIdParen($inner)
    {
        $parent = $this->parent;
        if (!$parent)
            return true;
        if ($parent instanceof LeanBinary) {
            if ($parent->lhs === $this)
                return get_class($parent)::$input_priority <= $inner->stack_priority;
            if ($parent->rhs === $this)
                return get_class($inner)::$input_priority > $parent->stack_priority;
        }
        return get_class($inner)::$input_priority > $parent->stack_priority;
    }

    public function latexArgs(&$syntax = null)
    {
        $matrixArgs = $this->matrixLatexArgs($syntax);
        if ($matrixArgs !== null)
            return $matrixArgs;
        $idInner = $this->idLatexInner();
        if ($idInner)
            return [$idInner->toLatex($syntax)];
        $args = $this->args;
        $func = $args[0];
        if ($this->is_MatProd())
            return $this->matProdLatexParts($syntax);
        if ($this->is_Expectation()) {
            $parts = array_slice($this->expectationLatexParts(), 1);
            return array_map(fn($n) => $n->toLatex($syntax), $parts);
        }
        if ($this->eye_positional_args($args)) {
            if ($syntax !== null)
                $syntax['eye'] = true;
            return [];
        }
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
        } elseif ($func instanceof LeanProperty && $func->rhs instanceof LeanToken && $func->rhs->text === 'choose' && (count($args) === 2 || count($args) === 3)) {
            $n = count($args) === 2 ? $func->lhs : $args[1];
            $k = count($args) === 2 ? $args[1] : $args[2];
            if ($n instanceof LeanParenthesis)
                $n = $n->arg;
            if ($k instanceof LeanParenthesis)
                $k = $k->arg;
            return [$n->toLatex($syntax), $k->toLatex($syntax)];
        }
        return parent::latexArgs($syntax);
    }

    public function latexFormat()
    {
        $rows = $this->matrixLatexSpec();
        if ($rows)
            return LeanAppend::bmatrixFormat(count($rows), count($rows[0]));
        if ($this->idLatexInner())
            return '%s';
        $args = $this->args;
        $func = $args[0];
        if ($this->is_Abs())
            return '\left|{%s}\right|';
        if ($this->is_MatProd())
            return '\\prod\\limits_{%s < %s} {%s}';
        if ($this->eye_positional_args($args))
            return '\\mathbb{I}';
        if ($this->is_Expectation())
            return $this->expectationLatexFormat($this->expectationLatexParts());
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
                    case 'choose':
                        if (count($args) == 2 || count($args) == 3)
                            return '\\binom{%s}{%s}';
                        break;
                }
            }
        }
        return implode("\\ ", array_fill(0, count($args), '{%s}'));
    }

    public function operand_count() {
        return $this->args[0]->operand_count();
    }

    public function strFormat()
    {
        return implode(' ', array_fill(0, count($this->args), '%s'));
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
                } elseif ($parent && $parent->func->is_parallel_operator())
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

}

class LeanArgsNewLineSeparated extends LeanArgs
{
    use LeanMultipleLine;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if (($parent = $this->parent) instanceof LeanCalc)
                    return LeanAssign::$input_priority - 1;
                if ($parent instanceof LeanArgsIndented) {
                    if (($grandparent = $parent->parent) instanceof LeanQuantifier)
                        // consider the following case of
                        // ∀ i ∈ s, cast 
                        //   (by sorry)
                        //   (x i) = y i
                        return LeanRelational::$input_priority + 1;
                    if ($grandparent instanceof LeanCalc)
                        // consider the following case of
                        //   calc _ ≤ _ := by sorry
                        //     _ < _ := by sorry
                        //     _ = _ := by sorry
                        return LeanAssign::$input_priority - 1;
                }
                return 47;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanIte([$caret], $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent) {
            if ($caret instanceof LeanParenthesis && $next == ':')
                return $caret;
            return parent::insert_newline($caret, $newline_count, $indent, $next);
        }
        if ($this->indent < $indent) {
            // Multiline app already has >=2 lines: next indented line is another arg,
            // not nested under a bare Property/Parenthesis (e.g. `(x).isLt` then more args).
            if (count($this->args) >= 2) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->push($caret);
                return $caret;
            }
            $wrapped = $this->push_args_indented($indent, $newline_count);
            if ($wrapped)
                return $wrapped;
            // Do not assign over $caret before reading $caret->level (PHP clobber bug).
            $caret = new LeanCaret($indent, $caret->level);
            $this->push($caret);
            return $caret;
        }

        if ($this->parent instanceof LeanAssign && !($caret instanceof LeanLineComment) && end($this->args) !== $caret)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if (end($this->args) === $caret) {
            for ($i = 0; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->push($caret);
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return false;
    }
    public function latexFormat()
    {
        return implode("\n", array_fill(0, count($this->args), '{%s}'));
    }

    public function push_newlines($newline_count)
    {
        for ($i = 0; $i < $newline_count; ++$i) {
            $this->push(new LeanCaret($this->indent, $this->level));
        }
        return end($this->args);
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

    public function strFormat()
    {
        return implode("\n", array_fill(0, count($this->args), '%s'));
    }

}

class LeanArgsIndented extends LeanBinary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                if ($this->parent instanceof LeanCalc)
                    return 17;
                if ($this->parent instanceof LeanQuantifier)
                    // consider the following case of
                    // ∀ i ∈ s, cast 
                    //   (by sorry)
                    //   (x i) = y i
                    return LeanRelational::$input_priority + 1;
                return 47;
            default:
                return parent::__get($vname);
        }
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            if ($new = $this->push_args_indented($indent, $newline_count))
                return $new;
            $this->rhs = new LeanArgsNewLineSeparated([$caret], $indent, $caret->level);
            return $this->rhs->push_newlines($newline_count);
        }
        if ($this->parent instanceof LeanAssign)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if (end($this->args) === $caret) {
            for ($i = 0; $i < $newline_count; ++$i) {
                $caret = new LeanCaret($indent, $caret->level);
                $this->push($caret);
            }
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        $parent = $this->parent;
        return $parent instanceof LeanStatements ||
            $parent instanceof LeanArgsNewLineSeparated ||
            ($parent instanceof LeanAssign && $parent->sep() === "\n");
    }

    public function latexFormat()
    {
        $sep = $this->sep();
        return "%s$sep%s";
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
    public function sep()
    {
        return "\n";
    }
    public function strFormat()
    {
        $sep = $this->sep();
        return "%s$sep%s";
    }

}

class LeanArgsCommaSeparated extends LeanArgs
{
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

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent, $caret->level));
                return $caret;
            } elseif ($this->parent)
                return $this->parent->insert($this, $func, $type);
        }
    }

    public function insert_comma($caret)
    {
        $caret = new LeanCaret($this->indent, $caret->level);
        $this->push($caret);
        return $caret;
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($caret instanceof LeanCaret && end($this->args) === $caret) {
            if ($this->indent > $indent)
                return parent::insert_newline($caret, $newline_count, $indent, $next);
            array_pop($this->args);
            $lineCaret = new LeanCaret($indent, $caret->level);
            $line = new LeanArgsCommaSeparated([$lineCaret], $indent, $caret->level);
            $parent = $this->parent;
            if ($parent instanceof LeanArgsCommaNewLineSeparated) {
                $parent->push($line);
                return $lineCaret;
            }
            $parent->replace($this, new LeanArgsCommaNewLineSeparated([$this, $line], $indent, $this->level));
            return $lineCaret;
        }
        return parent::insert_newline($caret, $newline_count, $indent, $next);
    }

    public function insert_tactic($caret, $token)
    {
        if ($caret instanceof LeanCaret)
            return $this->insert_word($caret, $token);
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanArgsCommaNewLineSeparated;
    }

    public function latexFormat()
    {
        return implode(", ", array_fill(0, count($this->args), '{%s}'));
    }

    public function strFormat()
    {
        return implode(", ", array_fill(0, count($this->args), '%s'));
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
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority - 1;
            default:
                return parent::__get($vname);
        }
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent, $caret->level));
                return $caret;
            } elseif ($this->parent)
                return $this->parent->insert($this, $func, $type);
        }
    }
    public function insert_semicolon($caret)
    {
        $caret = new LeanCaret($this->indent, $caret->level);
        $this->push($caret);
        return $caret;
    }

    public function insert_tactic($caret, $type)
    {
        if ($caret instanceof LeanCaret) {
            if (($this->parent instanceof LeanTactic) && $this->parent->is_inline_tactic_block() || $this->parent instanceof LeanBy) {
                $this->replace($caret, new LeanTactic($type, $caret, $this->indent, $caret->level));
                return $caret;
            }
            return $this->insert_word($caret, $type);
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        return implode("; ", array_fill(0, count($this->args), '{%s}'));
    }

    public function strFormat()
    {
        return implode("; ", array_fill(0, count($this->args), '%s'));
    }

}

class LeanArgsCommaNewLineSeparated extends LeanArgs
{
    use LeanMultipleLine;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 17;
            default:
                return parent::__get($vname);
        }
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new $func($caret, $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function insert_comma($caret)
    {
        $c2 = new LeanCaret($caret->indent, $caret->level);
        if ($caret instanceof LeanArgsCommaSeparated) {
            $caret->push($c2);
            return $c2;
        }
        $this->replace($caret, new LeanArgsCommaSeparated([$caret, $c2], $caret->indent, $caret->level));
        return $c2;
    }


    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        } else {
            if (end($this->args) === $caret) {
                if ($caret instanceof LeanArgsCommaSeparated) {
                    if (end($caret->args) instanceof LeanCaret)
                        array_pop($caret->args);
                    $lineCaret = new LeanCaret($indent, $caret->level);
                    $line = new LeanArgsCommaSeparated([$lineCaret], $indent, $caret->level);
                    $this->push($line);
                    return $lineCaret;
                }
                for ($i = 0; $i < $newline_count - 1; ++$i) {
                    $caret = new LeanCaret($indent, $caret->level);
                    $this->push($caret);
                }
                return $caret;
            }
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
    }

    public function is_indented()
    {
        return false;
    }

    public function latexFormat()
    {
        return implode(",\n", array_fill(0, count($this->args), '{%s}'));
    }

    public function strFormat()
    {
        return implode(",\n", array_fill(0, count($this->args), '%s'));
    }
}

// END OF args family (LeanSyntax stays in lean.php)
