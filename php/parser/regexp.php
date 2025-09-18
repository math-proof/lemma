<?php

class Regex
{

    public $parent;

    public function remove_negation() {
        return false;
    }

    public function delete() {
        $this->parent->removeChild($this);
    }
    
    public function is_possibly_empty()
    {
        return false;
    }

    public function __clone()
    {
        $this->parent = null;
    }

    public function rewrite($transform_fn)
    {}

    public function append($caret)
    {
        return $this->append_multiple("RegexComplex", $caret);
    }

    public function append_or()
    {
        $parent = $this->parent;
        return RegexOr::$input_precedence > $parent->stack_precedence ? $this->append_multiple("RegexOr", new RegexCaret()) : $parent->append_or();
    }

    public function append_multiple($Type, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $Type) {
            $parent->args[] = $caret;
            $caret->parent = $parent;
        } else {
            $parent->replace($this, new $Type([$this,$caret], $parent));
        }

        return $caret;
    }

    public function append_lexeme(&$word)
    {
        return $this->append(new RegexSimple($word));
    }

    public function append_postunary($Type)
    {
        $parent = $this->parent;
        $new = new $Type($this, $parent);
        $parent->replace($this, $new);
        return $new;
    }

    public function append_unary($Type)
    {
        $caret = new RegexCaret();
        $this->append(new $Type($caret));
        return $caret;
    }

    public function append_plus()
    {
        return $this->append_postunary("RegexPlus");
    }

    public function append_star()
    {
        return $this->append_postunary("RegexStar");
    }

    public function append_ques()
    {
        return $this->append_postunary("RegexQues");
    }

    public function append_left_bracket()
    {
        return $this->append_unary("RegexCharProperty");
    }

    public function append_left_brace($transform_fn=null)
    {
        $parent = $this->parent;
        if ($transform_fn) {
            if ($parent instanceof RegexCharProperty) {
                return $this->append(new RegexSimple("{"));
            }
            
            return $this->append_unary("RegexCurly");
        }
        else {
            if ($parent instanceof RegexCharProperty) {
                return $this->append(new RegexSimple("{"));
            }
            
            if ($parent instanceof RegexComplex || $parent instanceof RegexOr) {
                $args = &$parent->args;
                $length = count($args);
                $args[$length - 1] = new RegexCurly($args[$length - 1], null, null, $parent);
                return $args[$length - 1];
            }

            if ($parent instanceof RegexSentence || $parent instanceof RegexGroupCaptured) {
                $parent->arg = new RegexCurly($parent->arg, null, null, $parent);
                return $parent->arg;
            }

            return $this->append_unary("RegexCurly");
        }
    }
    
    public function append_right_brace($transform_fn=null)
    {
        $parent = $this->parent;
        if ($parent instanceof RegexCharProperty) {
            return $this->append(new RegexSimple("}"));
        }
        
        $caret = $this;
        $old = $this;
        for (;;) {
            if ($caret === null) {
                error_log("unnecessary right brace at position detected");
                break;
            }
            
            if ($caret instanceof RegexCurly) {
                break;
            }
            
            $old = $caret;
            $caret = $caret->parent;
        }

        if ($caret === null) {
            $caret = $old;
        }
        
        return $caret;
    }
    
    public function append_left_parenthesis($type)
    {
        return $this->append_unary(RegexGroup::getType($type));
    }

    public function __construct($parent = null)
    {
        $this->parent = $parent;
    }

    public function is_or_structure()
    {
        return false;
    }

    public function has_or_structure()
    {
        return false;
    }

    public function match_length() {
        return null;
    }
    
    public function has_group_captured() {
        return false;
    }
    
    static public function test()
    {
        $regex = "\b";

        $regex = Regex::compile($regex);

        $regex->rewrite(true);

        error_log("regex = ".$regex);
        
        error_log("match_length = ".$regex->match_length());
    }

    public function append_right_bracket()
    {
        $caret = $this;
        $old = $this;
        for (;;) {
            if ($caret === null) {
                error_log("unnecessary right bracket at position detected");
                break;
            }
            $old = $caret;
            $caret = $caret->parent;
            if ($caret instanceof RegexCharProperty) {
                break;
            }
        }
        if ($caret === null) {
            $caret = $old;
        }

        return $caret;
    }

    public function append_right_parenthesis()
    {
        $caret = $this;
        $old = $this;
        for (;;) {
            if ($caret === null) {
                error_log("unnecessary right parenthesis at position detected");
                break;
            }
            $old = $caret;
            $caret = $caret->parent;
            if ($caret instanceof RegexCharProperty) {
                $word = ")";
                return $old->append_lexeme($word);
            }

            if ($caret instanceof RegexGroup) {
                break;
            }
        }

        if ($caret === null) {
            $caret = $old;
        }

        return $caret;
    }

    static public function compile($regex, $transform_fn=true)
    {
        $caret = new RegexCaret();
        $root = new RegexSentence($caret);
        $length = strlen($regex);
        for ($i = 0; $i < $length;) {
            switch ($regex[$i]) {
                case '(':
                    if ($caret->parent instanceof RegexCharProperty) {
                        $word = "(";
                        $caret = $caret->append_lexeme($word);
                        break;
                    }
                    
                    $type = '';
                    if ($regex[$i + 1] == '?') {
                        switch ($regex[$i + 2]) {
                            case ':':
                                $type = "?:";
                                $i += 2;
                                break;
                            case '=':
                                $type = "?=";
                                $i += 2;
                                break;
                            case '!':
                                $i += 2;
                                $type = "?!";
                                break;
                            case '<':
                                switch ($regex[$i + 3]) {
                                    case '=':
                                        $type = "?<=";
                                        $i += 3;
                                        break;
                                    case '!':
                                        $type = "?<!";
                                        $i += 3;
                                        break;
                                    default:
                                        break;
                                }
                                break;
                        }
                    }
                    $caret = $caret->append_left_parenthesis($type);
                    break;

                case ')':
                    $caret = $caret->append_right_parenthesis();
                    break;

                case '|':
                    $caret = $caret->append_or();
                    break;

                case '{':
                    $caret = $caret->append_left_brace($transform_fn);
                    break;
                case '}':
                    $caret = $caret->append_right_brace($transform_fn);
                    break;

                case '[':
                    $caret = $caret->append_left_bracket();
                    break;
                case ']':
                    $caret = $caret->append_right_bracket();
                    break;

                case '*':
                    $caret = $caret->append_star();
                    break;

                case '+':
                    $caret = $caret->append_plus();
                    break;

                case '?':
                    $caret = $caret->append_ques();
                    break;

                case '\\':
                    $word = "\\" . $regex[$i + 1];
                    $caret = $caret->append_lexeme($word);
                    ++ $i;
                    break;

                default:
                    if (preg_match("/[^\\\\(){}|\[\]*+?]+/", $regex, $m, PREG_OFFSET_CAPTURE, $i)) {
                        [$mText,$index] = $m[0];
                        $i = strlen($mText) + $index - 1;
                        $caret = $caret->append_lexeme($mText);
                        break;
                    } else
                        throw "lexeme not found!";
            }
            ++ $i;
        }

        return $root;
    }
}

class RegexCaret extends Regex
{

    public function __toString()
    {
        return "";
    }

    public function append($new)
    {
        $parent = $this->parent;
        $new->parent = $parent;
        $parent->replace($this, $new);
        return $new;
    }

    public function is_possibly_empty()
    {
        return true;
    }
}

class RegexSimple extends Regex
{

    public $arg;

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
    }

    public function __toString()
    {
        return $this->arg;
    }

    public function split()
    {
        $chars = $this->chars();
        $parent = $this->parent;
        $last = array_pop($chars);
        return [
            new RegexSimple(implode("",
                array_map(fn(&$m) => $m[0][0], $chars)), $parent),
            new RegexSimple($last[0][0], $parent)];
    }

    public function chars() {
        return std\matchAll("/([\\\\])?(.)/u", $this->arg);
    }
    
    public function __get($vname)
    {
        switch ($vname) {
            case 'length':
                return count($this->chars());
        }
    }

    public function append_postunary($Type)
    {
        if ($this->length > 1) {
            [$former, $latter] = $this->split();

            $parent = $this->parent;
            if ($parent instanceof RegexComplex) {
                $parent->args[count($parent->args) - 1] = $former;
                $parent->args[] = $latter;
            } else {
                $parent->replace($this, new RegexComplex([$former,$latter], $parent));
            }
            return $latter->append_postunary($Type);
        } else {
            return parent::append_postunary($Type);
        }
    }

    public function is_possibly_empty()
    {
        foreach ($this->chars() as [&$m,$index]) {
            if ($m[1]) {
                switch ($m[2]) {
                    //https://www.regular-expressions.info/wordboundaries.html
                    case 'b':
                    case 'B':
                    case 'y':
                    case 'Y':
                    case 'm':
                    case 'M':
                        break;
                    default:
                        return false;
                }
            } else {
                switch ($m[2]) {
                    case '^':
                    case '$':
                        break;
                    default:
                        return false;
                }
            }
        }

        return true;
    }
    
    public function append($new)
    {
        if ($new instanceof self) {
            $this->arg .= $new->arg;
            return $this;
        }
        else
            return parent::append($new);
    }
    
    public function match_length() {
        $match_length = 0;
        foreach ($this->chars() as [&$m,$index]) {
            if ($m[1]) {
                switch ($m[2]) {
                    //https://www.regular-expressions.info/wordboundaries.html
                    case 'b':
                    case 'B':
                    case 'y':
                    case 'Y':
                    case 'm':
                    case 'M':
                        break;
                    default:
                        ++$match_length;
                        break;
                }
            } else {
                switch ($m[2]) {
                    case '^':
                    case '$':
                        break;
                    default:
                        ++$match_length;
                        break;
                }
            }
        }
        
        return $match_length;
    }

    public function remove_negation() {
        if ($this->arg[0] == '!') {
            $this->arg = std\substring($this->arg, 1);
            if (!$this->arg) {
                $this->delete();
            }
            return true;
        }
    }
}

class RegexUnary extends Regex
{

    public $arg;

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
        $arg->parent = $this;
    }

    public function replace($old, $new)
    {
        $this->arg = $new;
    }

    public function rewrite($transform_fn)
    {
        $this->arg->rewrite($transform_fn);
    }

    public function __clone()
    {
        parent::__clone();
        $this->arg = clone $this->arg;
        $this->arg->parent = $this;
    }
    
    public function has_group_captured() {
        return $this->arg->has_group_captured();
    }
    
    public function match_length() {
        return $this->arg->match_length();
    }
    
    public function removeChild($node) {
        $this->parent->removeChild($this);
    }
}

class RegexMultiple extends Regex
{

    public $args;

    public function __construct($args, $parent = null)
    {
        parent::__construct($parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function has_or_structure()
    {
        return std\array_any(fn ($arg) => $arg->has_or_structure(), $this->args);
    }
    
    public function has_group_captured() {
        return std\array_any(fn ($arg) => $arg->has_group_captured(), $this->args);
    }
    
    public function replace($old, $new)
    {
        $i = std\indexOf($this->args, $old);
        if ($i < 0) {
            throw new Exception("replace(old, replacement)");
        }

        if (is_array($new)) {
            array_splice($this->args, $i, 1, $new);
        }
        else {
            $this->args[$i] = $new;
        }
    }

    public function rewrite($transform_fn)
    {
        foreach ($this->args as $arg) {
            $arg->rewrite($transform_fn);
        }
    }

    public function __clone()
    {
        parent::__clone();
        foreach ($this->args as &$arg) {
            $arg = clone $arg;
            $arg->parent = $this;
        }
    }
    
    public function removeChild($node) {
        $i = std\indexOf($this->args, $node);
        if ($i < 0)
            throw new Exception("removeChild(\$node)");
        std\array_delete($this->args, $i);
        
        if (count($this->args) == 1) {
            [$arg] = $this->args;
            $parent = $this->parent;
            $parent->replace($this, $arg);
            $arg->parent = $parent;
        }
    }

    public function remove_negation() {
        return $this->args[0]->remove_negation();
    }
}

class RegexComplex extends RegexMultiple
{

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 3;
        }
    }

    public function __toString()
    {
        return implode("", array_map(fn ($arg) => "$arg", $this->args));
    }

    public function is_possibly_empty()
    {
        foreach ($this->args as $arg) {
            if (! $arg->is_possibly_empty()) {
                return false;
            }
        }

        return true;
    }

    public function search_for_NegativeLookBehind() {
        $lookBehind = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof RegexGroupNegativeLookBehind) {
                $lookBehind[] = $arg;
            }
        }
        
        if (!$this->has_group_captured() && count($lookBehind) == 1) {
            [$lookBehind] = $lookBehind;
            if ($lookBehind->arg->match_length() === null)
                return $lookBehind;
        }
    }
    
    public function search_for_LookBehind() {
        $lookBehind = [];
        foreach ($this->args as $arg) {
            if ($arg instanceof RegexGroupLookBehind) {
                $lookBehind[] = $arg;
            }
        }
        
        if (!$this->has_group_captured() && count($lookBehind) == 1) {
            [$lookBehind] = $lookBehind;
            if ($lookBehind->arg->match_length() === null)
                return $lookBehind;
        }
    }
    
    public function rewrite($transform_fn) {
        $self = $this->search_for_NegativeLookBehind();
        if ($self)
            return $this->rewrite_NegativeLookBehind($self, $transform_fn);
        
        $self = $this->search_for_LookBehind();
        if ($self)
            return $this->rewrite_LookBehind($self, $transform_fn);

        foreach ($this->args as $arg) {
            $arg->rewrite($transform_fn);
        }
    }

    public function rewrite_LookBehind($self, $transform_fn)
    {
        $index = std\indexOf($this->args, $self);

        $textBefore = std\slice($this->args, 0, $index);

        if ($textBefore) {
            if ($index == 1) {
                [$textBefore] = $textBefore;
            } else {
                $textBefore = new RegexComplex($textBefore);
            }

            $textBefore = new RegexGroupLookAhead($textBefore);
            // $textBefore = "(?=$textBefore)";
        } else {
            $textBefore = null;
        }

        $textFocused = std\slice($this->args, $index + 1);

        $size = count($textFocused);
        if ($size) {
            if ($size == 1) {
                [$textFocused] = $textFocused;
            } else {
                $textFocused = new RegexComplex($textFocused);
            }

            if ($textFocused instanceof RegexOr) {
                $textFocused = new RegexGroupUnCaptured($textFocused);
            }
        } else {
            $textFocused = null;
        }
        
        $look_behind_value = $self->arg;
        if ($textBefore) {
            if ($look_behind_value instanceof RegexOr) {
                $look_behind_value = new RegexGroupUnCaptured($look_behind_value);
            }
            
            $lookahead = new RegexGroupLookAhead(
                new RegexComplex([$textBefore, $look_behind_value]));
        }
        else {
            $lookahead = new RegexGroupLookAhead($look_behind_value);
        }
        
        $lookahead->parent = $this;
        $this->replace($self, [$lookahead, new RegexStar(new RegexSimple($transform_fn? "[^{}]": "."), $this)]);
        
        array_splice($this->args, 0, $index);
        //for example:
        //[a-z]+(?<=(?:is|be|are) +)selected
        //(?=[a-z]+(?:is|be|are) +)[^{}]*selected
    }
    
    public function rewrite_NegativeLookBehind($self, $transform_fn)
    {
        $index = std\indexOf($this->args, $self);

        $textBefore = std\slice($this->args, 0, $index);

        if ($textBefore) {
            if ($index == 1) {
                [$textBefore] = $textBefore;
            } else {
                $textBefore = new RegexComplex($textBefore);
            }

            $textBefore = new RegexGroupLookAhead($textBefore);
            // $textBefore = "(?=$textBefore)";
        } else {
            $textBefore = null;
        }

        $textFocused = std\slice($this->args, $index + 1);

        $size = count($textFocused);
        if ($size) {
            if ($size == 1) {
                [$textFocused] = $textFocused;
            } else {
                $textFocused = new RegexComplex($textFocused);
            }

            if ($textFocused instanceof RegexOr) {
                $textFocused = new RegexGroupUnCaptured($textFocused);
            }
        } else {
            $textFocused = null;
        }

        $look_behind_value = $self->arg;
        if ($look_behind_value instanceof RegexComplex) {
            if ($textFocused) {
                $look_behind_value->args[] = $textFocused;
                $textFocused->parent = $look_behind_value;
            }
        } else {
            if ($look_behind_value instanceof RegexOr) {
                $look_behind_value = new RegexGroupUnCaptured($look_behind_value);
            }
            if ($textFocused) {
                $look_behind_value = new RegexComplex([$look_behind_value,$textFocused]);
            }
        }

        // $lookahead = "(?!$look_behind_value(?:$textFocused))";
        $lookahead = new RegexGroupNegativeLookAhead($look_behind_value);

        //look before your leap:
        $lookahead = new RegexStar(new RegexGroupUncaptured(new RegexComplex([clone $lookahead, new RegexSimple($transform_fn? "[^{}]": ".")])));
        // firstly, there is no character which is postpended with $look_behind_value before $value;
        // secondly, there is some character is postpended with $look_behind_value before $value, but there are some characters inbwteen them:
        
        $lookahead->parent = $this;
        $this->replace($self, $lookahead);
        
        if ($textBefore) {
            $this->replace($this->args[0], $textBefore);
            array_splice($this->args, 1, $index - 1);
        } else {
            std\array_insert($this->args, 0, new RegexSimple("^"));
            //array_splice($this->args, 0, $index);
        }
        //for example:
        //[a-z]+(?<!(?:\bpo|fami))ly
        //(?=\\b[a-z]+)(?:(?!(?:\\bpo|fami)ly)[^{}])*ly
    }
    
    public function match_length() {
        $match_length = 0;
        foreach ($this->args as $arg) {
            $match_length_ = $arg->match_length();
            if ($match_length_ === null)
                return null;
            
            $match_length += $match_length_;
        }
        
        return $match_length;
    }
}

class RegexCharProperty extends RegexUnary
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "[$this->arg]";
    }

    public function is_possibly_empty()
    {
        return false;
    }
    
    public function match_length() {
        return 1;
    }
}

class Quantifier extends RegexUnary {
    
    public function match_length() {
        return null;
    }
}

class RegexLazy extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "$this->arg?";
    }

    public function is_possibly_empty()
    {
        return true;
    }
}

class RegexPossessive extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "$this->arg+";
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty();
    }
}

class RegexQues extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "$this->arg?";
    }

    public function is_possibly_empty()
    {
        return true;
    }
}

class RegexStar extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "$this->arg*";
    }

    public function is_possibly_empty()
    {
        return true;
    }
}

class RegexPlus extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function __toString()
    {
        return "$this->arg+";
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty();
    }
}

class RegexCurly extends Quantifier
{

    public static $input_precedence = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public $cmin;

    public $cmax;

    public function __construct($arg, $cmin, $cmax, $parent = null)
    {
        parent::__construct($arg, $parent);
        $this->cmin = $cmin;
        $this->cmax = $cmax;
    }

    public function __toString()
    {
        if ($this->cmin === null) {
            return "$this->arg{,$this->cmax}";
        }

        if ($this->cmax === null) {
            return "$this->arg{{$this->cmin},}";
        }

        if ($this->cmin == $this->cmax)
            return "$this->arg{{$this->cmin}}";

        return "$this->arg{{$this->cmin},$this->cmax}";
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty() && $this->cmin <= 0;
    }
    
    public function match_length() {
        if ($this->cmin == $this->cmax);
            return $this->cmax;
        return null;
    }
    
    public function append($new)
    {
        if ($new instanceof RegexSimple && $this->cmin == null && $this->cmax == null) {
            $arg = $new->arg;
            [$cmin, $cmax] = explode(',', $arg);
            if ($cmax === null)
                $cmax = $cmin;
            $this->cmax = $cmax;
            $this->cmin = $cmin;
            return $this;
        }
        return parent::append($new);
    }
    
}

class RegexOr extends RegexMultiple
{

    public static $input_precedence = 3;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function is_or_structure()
    {
        return true;
    }

    public function has_or_structure()
    {
        return true;
    }

    public function __toString()
    {
        return implode("|", array_map(fn ($arg) => "$arg", $this->args));
    }

    public function is_possibly_empty()
    {
        foreach ($this->args as $arg) {
            if ($arg->is_possibly_empty())
                return true;
        }

        return false;
    }
    
    public function match_length() {
        $match_length = 0;
        foreach ($this->args as $arg) {
            $match_length_ = $arg->match_length();
            if ($match_length_ === null)
                return null;
            
            if ($match_length_ == 0)
                continue;
            
            if (!$match_length)
                $match_length = $match_length_;
            
            if ($match_length != $match_length_)
                return null;
        }
        
        return $match_length;
    }
}

class RegexGroup extends RegexUnary
{

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 2;
        }
    }

    public function has_or_structure()
    {
        return $this->arg->has_or_structure();
    }

    static public function getType($type)
    {
        switch ($type) {
            case '?:':
                return "RegexGroupUncaptured";
            case '?=':
                return "RegexGroupLookAhead";
            case '?!':
                return "RegexGroupNegativeLookAhead";
            case '?<=':
                return "RegexGroupLookBehind";
            case '?<!':
                return "RegexGroupNegativeLookBehind";
            default:
                return "RegexGroupCaptured";
        }
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty();
    }
}

class RegexGroupCaptured extends RegexGroup
{
    
    public function __toString()
    {
        return "($this->arg)";
    }
    
    public function has_group_captured() {
        return true;
    }
    
    public function match_length() {
        return $this->arg->match_length();
    }

    public function remove_negation() {
        return $this->arg->remove_negation();
    }
}

class RegexGroupUncaptured extends RegexGroup
{

    public function __toString()
    {
        return "(?:$this->arg)";
    }
    
    public function match_length() {
        return $this->arg->match_length();
    }
    
    public function remove_negation() {
        return $this->arg->remove_negation();
    }
}

// www.regular-expressions.info/lookaround.html
class RegexGroupLookAround extends RegexGroup
{

    public function is_possibly_empty()
    {
        return true;
    }
    
    public function match_length() {
        return 0;
    }
}

class RegexGroupLookBehind extends RegexGroupLookAround
{

    public function __toString()
    {
        return "(?<=$this->arg)";
    }
}

class RegexGroupNegativeLookBehind extends RegexGroupLookAround
{

    public function __toString()
    {
        return "(?<!$this->arg)";
    }
}

class RegexGroupLookAhead extends RegexGroupLookAround
{

    public function __toString()
    {
        return "(?=$this->arg)";
    }
}

class RegexGroupNegativeLookAhead extends RegexGroupLookAround
{

    public function __toString()
    {
        return "(?!$this->arg)";
    }
}

class RegexSentence extends RegexUnary
{

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_precedence':
                return 0;
        }
    }

    public function __toString()
    {
        return "$this->arg";
    }

    public function is_possibly_empty()
    {
        return $this->arg->is_possibly_empty();
    }
    
    public function is_or_structure()
    {
        return $this->arg->is_or_structure();
    }
}

?>