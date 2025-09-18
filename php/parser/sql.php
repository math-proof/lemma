<?php
require_once dirname(__file__).'/../std.php';
ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'SQLAdd',
    '-' => 'SQLSub',
    '*' => 'SQLMul',
    '/' => 'SQLDiv',
    '%' => 'SQLMod',
    '&' => 'SQLBitAnd',
    '|' => 'SQLBitOr',
    '^' => 'SQLBitXor',
    '<<' => 'SQLSHL',
    '>>' => 'SQLSHR',
    '||' => 'SQLOr',
    '&&' => 'SQLAnd'
];

abstract class SQL implements JsonSerializable
{

    public $parent;

    public function remove_negation()
    {
        return false;
    }

    public function delete()
    {
        $this->parent->removeChild($this);
    }

    public function insert_case($caret)
    {
        return $caret->push_case();
    }

    public function insert_when($caret)
    {
        return $this->parent->insert_when($this);
    }
    public function insert_then($caret)
    {
        return $this->parent->insert_then($this);
    }
    public function insert_end($caret)
    {
        return $this->parent->insert_end($this);
    }
    public function append_from()
    {
        return $this->parent->append_from();
    }

    public function append_set()
    {
        return $this->parent->append_set();
    }

    public function append_where()
    {
        return $this->parent->append_where();
    }

    public function append_on()
    {
        return $this->parent->append_on();
    }

    public function insert_order($caret)
    {
        return $this->parent->insert_order($this);
    }

    public function insert_group($caret)
    {
        return $this->parent->insert_group($this);
    }

    public function append_having()
    {
        return $this->parent->append_having();
    }

    public function append_limit()
    {
        return $this->parent->append_limit();
    }

    public function append_offset()
    {
        return $this->parent->append_offset();
    }

    public function append_space($token)
    {
        $parent = $this->parent;
        return $parent instanceof SQLPairedGroup ? $this->append_token($token) : $this;
    }

    public function append($new)
    {
        return $this->parent->append($new);
    }

    public function __clone()
    {
        $this->parent = null;
    }

    public function append_binary($type)
    {
        $parent = $this->parent;
        if ($type::$input_priority > $parent->stack_priority) {
            $new = new SQLCaret();
            $parent->replace($this, new $type($this, $new));
            return $new;
        } else
            return $this->parent->append_binary($type);
    }

    public function append_arithmetic($token)
    {
        if ($this->parent instanceof SQLPairedGroup)
            return $this->append_token($token);
        global $token2classname;
        return $this->append_binary($token2classname[$token]);
    }
    public function append_or()
    {
        $parent = $this->parent;
        return SQLOr::$input_priority > $parent->stack_priority ? $this->append_multiple("SQLOr", new SQLCaret()) : $parent->append_or();
    }

    public function append_multiple($Type, $caret)
    {
        $parent = $this->parent;
        if ($parent instanceof $Type) {
            $parent->args[] = $caret;
            $caret->parent = $parent;
        } else
            $parent->replace($this, new $Type([$this, $caret], $parent));

        return $caret;
    }

    public function append_token(&$word)
    {
        return $this->append(new SQLToken($word));
    }

    public function insert_comma($caret)
    {
        return $this->parent->insert_comma($caret);
    }

    public function insert_apostrophe($caret)
    {
        return $caret->append('SQLApostrophe');
    }

    public function append_semicolon()
    {
        return $this->parent->append_semicolon();
    }

    public function append_unary_operator($func)
    {
        $caret = new SQLCaret();
        $this->append(new SQLOperator($func, $caret));
        return $caret;
    }

    public function __construct($parent = null)
    {
        $this->parent = $parent;
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
            if ($caret instanceof SQLCharProperty) {
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
        return $this->parent->append_right_parenthesis();
    }

    public function append_dot()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_minus()
    {
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_operator($caret, $func)
    {
        return $this->parent->insert_operator($this, $func);
    }
    public function append_using()
    {
        return $this->parent->append_using();
    }

    static public function compile($sql, $transform_fn = true)
    {
        $caret = new SQLCaret();
        $root = new SQLSentence([$caret]);
        $tokens = array_map(fn($match) => $match[0][0], std\matchAll('/\w+|\W/', $sql));
        $i = 0;
        $count = count($tokens);
        while ($i < $count) {
            $token = $tokens[$i];
            switch (strtolower($token)) {
                case 'select':
                case 'update':
                case 'delete':
                    $Type = std\capitalize($token);
                    $caret = $caret->append("SQL$Type");
                    break;

                case ' ':
                case "\t":
                case "\r":
                case "\n":
                    $caret = $caret->append_space($token);
                    break;

                case '.':
                    $caret = $caret->append_dot();
                    break;

                case 'group':
                case 'order':
                    $j = 1;
                    while ($i + $j < $count && std\isspace($tokens[$i + $j]))
                        ++$j;

                    if ($i + $j < $count && strtolower($tokens[$i + $j]) == 'by') {
                        $func = "insert_$token";
                        $caret = $caret->parent->$func($caret);
                        $i += $j;
                    } else
                        $caret = $caret->append_token($token);
                    break;

                case 'from':
                case 'where':
                case 'limit':
                case 'offset':
                case 'having':
                case 'using':
                case 'on':
                case 'set':
                    $func = "append_$token";
                    $caret = $caret->parent->$func();
                    break;

                case "'":
                    $caret = $caret->parent->insert_apostrophe($caret);
                    break;
                case '"':
                    $caret = $caret->parent instanceof SQLApostrophe || $caret->parent instanceof SQLGraveAccent ?
                        $caret->append_token($token) :
                        $caret->append('SQLQuotation');
                    break;
                case '`':
                    $caret = $caret->parent instanceof SQLApostrophe || $caret->parent instanceof SQLQuotation ?
                        $caret->append_token($token) :
                        $caret->append('SQLGraveAccent');
                    break;

                case 'regexp':
                case 'like':
                case 'and':
                case 'or':
                case 'as':
                case 'join':
                case 'in':
                    $Type = std\capitalize($token);
                    $caret = $caret->append_binary("SQL$Type");
                    break;

                case 'is':
                    $Type = std\capitalize($token);
                    $Type = "SQL$Type";
                    $not = $i + 2 < $count && std\isspace($tokens[$i + 1]) &&
                        strtolower($tokens[$i + 2]) == 'not';
                    if ($not) {
                        $Type .= 'Not';
                        $i += 2;
                    }

                    $caret = $caret->append_binary($Type);
                    break;
                case '(':
                    $caret = $caret->parent->insert_left_parenthesis($caret);
                    break;

                case ')':
                    $caret = $caret->parent->append_right_parenthesis();
                    break;

                case '\\':
                    $word = "\\" . $tokens[$i + 1];
                    $caret = $caret->append_token($word);
                    ++$i;
                    break;

                case '<':
                    if ($caret->parent instanceof SQLPairedGroup)
                        $caret = $caret->append_token($token);
                    else {
                        $hit = false;
                        if ($i + 1 < $count) {
                            switch ($tokens[$i + 1]) {
                                case '=':
                                    $caret = $caret->append_binary('SQLLe');
                                    $hit = true;
                                    break;
                                case '>':
                                    $caret = $caret->append_binary('SQLNe');
                                    $hit = true;
                                    break;
                                case '<':
                                    $token .= '<';
                                    $caret = $caret->append_arithmetic($token);
                                    $hit = true;
                                    break;
                            }
                        }
                        if ($hit)
                            ++$i;
                        else
                            $caret = $caret->append_binary('SQLLt');
                    }
                    break;

                case '>':
                    if ($caret->parent instanceof SQLPairedGroup)
                        $caret = $caret->append_token($token);
                    else {
                        if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                            $caret = $caret->append_binary('SQLGe');
                            ++$i;
                        } elseif ($i + 1 < $count && $tokens[$i + 1] == '>') {
                            $token .= '>';
                            $caret = $caret->append_arithmetic($token);
                            ++$i;
                        } else
                            $caret = $caret->append_binary('SQLGt');
                    }
                    break;

                case '=':
                    $caret = $caret->append_binary('SQLEq');
                    break;

                case '!':
                    if ($i + 1 < $count && $tokens[$i + 1] == '=') {
                        $caret = $caret->append_binary('SQLNe');
                        ++$i;
                    } else
                        $caret = $caret->append_unary_operator('not');
                    break;

                case 'with':
                    if ($caret->parent instanceof SQLApostrophe || $caret->parent instanceof SQLGraveAccent || $caret->parent instanceof SQLQuotation)
                        $caret = $caret->append_token($token);
                    else {
                        $recursive = $i + 2 < $count && std\isspace($tokens[$i + 1]) &&
                            strtolower($tokens[$i + 2]) == 'recursive';
                        $caret = $caret->append_with($recursive);
                        if ($recursive)
                            $i += 2;
                    }
                    break;

                case ',':
                    $caret = $caret->parent->insert_comma($caret);
                    break;

                case 'inner':
                case 'cross':
                case 'left':
                case 'right':
                case 'full':
                    $j = 1;
                    while ($i + $j < $count && std\isspace($tokens[$i + $j]))
                        ++$j;

                    if ($i + $j < $count && strtolower($tokens[$i + $j]) == 'join') {
                        $Type = std\capitalize($token);
                        $caret = $caret->append_binary("SQL{$Type}Join");
                        $i += $j;
                    } else
                        $caret = $caret->append_token($token);
                    break;

                case 'path':
                case 'distinct':
                case 'separator':
                    $caret = $caret->parent->insert_operator($caret, $token);
                    break;

                case 'not':
                    if ($caret->parent instanceof SQLApostrophe || $caret->parent instanceof SQLGraveAccent || $caret->parent instanceof SQLQuotation)
                        $caret = $caret->append_token($token);
                    else {
                        $j = 1;
                        while ($i + $j < $count && std\isspace($tokens[$i + $j]))
                            ++$j;

                        if ($i + $j < $count) {
                            $next_token = $tokens[$i + $j];
                            $hit = std\fullmatch('/in|like|regexp/i', $next_token);
                        } else
                            $hit = false;

                        if ($hit) {
                            $Type = std\capitalize($token);
                            $next_token = std\capitalize($next_token);
                            $caret = $caret->append_binary("SQL{$Type}$next_token");
                            $i += $j;
                        } else
                            $caret = $caret->append_unary_operator('not');
                    }
                    break;

                case ';':
                    $caret = $caret->parent->append_semicolon();
                    break;

                case 'union':
                    $Type = std\capitalize($token);
                    $Type = "SQL$Type";
                    $all = $i + 2 < $count && std\isspace($tokens[$i + 1]) &&
                        strtolower($tokens[$i + 2]) == 'all';
                    if ($all) {
                        $Type .= 'All';
                        $i += 2;
                    }

                    $caret = $caret->append_binary($Type);
                    break;

                case '-':
                    if ($i + 1 < $count && $tokens[$i + 1] == '>') {
                        $json_unquote = $i + 2 < $count && $tokens[$i + 2] == '>';
                        $caret = $caret->append_binary($json_unquote ? 'SQLJsonExtractUnquote' : 'SQLJsonExtract');
                        if ($json_unquote)
                            $i += 2;
                        else
                            ++$i;
                        break;
                    }
                    if ($i + 2 < $count && $tokens[$i + 1] == '-' && $tokens[$i + 2] == ' ') {
                        $i += 2;
                        // line comment;
                        while (true) {
                            ++$i;
                            if ($i >= $count || $tokens[$i] == "\n")
                                break;
                        }
                        --$i; // now $tokens[++$i] must be a new line or the end of line;
                        break;
                    }
                    $caret = $caret->append_arithmetic($token);
                    break;

                case '*':
                    if ($caret instanceof SQLCaret)
                        $caret = $caret->append_token($token);
                    else
                        $caret = $caret->append_arithmetic($token);
                    break;

                case '+':
                case '/':
                case '%':
                case '^':
                    $caret = $caret->append_arithmetic($token);
                    break;

                case '&':
                    if ($i + 1 < $count && $tokens[$i + 1] == '&') {
                        ++$i;
                        $token .= '&';
                    }
                    $caret = $caret->append_arithmetic($token);
                    break;

                case '|':
                    if ($i + 1 < $count && $tokens[$i + 1] == '|') {
                        ++$i;
                        $token .= '|';
                    }
                    $caret = $caret->append_arithmetic($token);
                    break;

                case 'case':
                    $caret = $caret->parent->insert_case($caret);
                    break;
                case 'when':
                    $caret = $caret->parent->insert_when($caret);
                    break;
                case 'then':
                    $caret = $caret->parent->insert_then($caret);
                    break;
                case 'end':
                    $caret = $caret->parent->insert_end($caret);
                    break;
                case 'desc':
                    $caret = $caret->parent->insert_desc($caret);
                    break;
                default:
                    $caret = $caret->append_token($token);
            }
            ++$i;
        }

        return $root;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                return $this->parent->root;
        }
    }

    public function replace_args(&$select, $old, $new)
    {
        if (std\is_list($select)) {
            $i = std\index($select, $old);
            if ($i >= 0) {
                $select[$i] = $new;
                if (!$new->parent)
                    $new->parent = $this;
                return true;
            }
        } elseif ($select === $old) {
            $select = $new;
            if (!$new->parent)
                $new->parent = $this;

            return true;
        }
    }

    public function insert_left_parenthesis($caret)
    {
        return $caret->append_left_parenthesis();
    }
}

class SQLCaret extends SQL
{

    public function __toString()
    {
        return "";
    }

    public function append($new)
    {
        if (is_string($new)) {
            $this->parent->replace($this, new $new($this));
            return $this;
        } else {
            $this->parent->replace($this, $new);
            return $new;
        }
    }

    public function append_with($recursive)
    {
        $this->parent->replace($this, new SQLWith($this, null, null, $recursive));
        return $this;
    }

    public function jsonSerialize(): mixed
    {
        return "";
    }

    public function append_left_parenthesis()
    {
        $this->parent->replace($this, new SQLParenthesis($this));
        return $this;
    }

    public function push_case()
    {
        $this->parent->replace($this, new SQLCase($this));
        return $this;
    }
    public function push_when()
    {
        $this->parent->replace($this, new SQLWhen($this));
        return $this;
    }
}

class SQLToken extends SQL
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

    public function append_token(&$word)
    {
        if (std\fullmatch("/\w+/", $this->arg) && std\fullmatch("/\w+/", $word)) {
            $new = new SQLToken($word);
            $this->parent->replace($this, new SQLArgsSpaceSeparated([$this, $new]));
            return $new;
        }

        $this->arg .= $word;
        return $this;
    }

    public function append_left_parenthesis()
    {
        $new = new SQLCaret();
        $this->parent->replace($this, new SQLFunction($this, $new));
        return $new;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'length':
                return strlen($this->arg);
            default:
                return parent::__get($vname);
        }
    }

    public function append_dot()
    {
        $parent = $this->parent;
        if (
            $parent instanceof SQLStatement && $this === $parent->from ||
            ($parent instanceof SQLSelect || $parent instanceof SQLFunction || $parent instanceof SQLAbstractJoin || $parent instanceof SQLRelational || $parent instanceof SQLLogical || $parent instanceof SQLArithmetic || $parent instanceof SQLUpdate || $parent instanceof SQLWhen) &&
            $this->is_variable()
        ) {
            $caret = new SQLCaret();
            $parent->replace($this, new SQLDot($this, $caret));
            return $caret;
        } else {
            $this->arg .= '.';
            return $this;
        }
    }

    public function append($new)
    {
        return $this->parent->append($new);
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg;
    }

    public function is_variable()
    {
        return std\fullmatch('/[a-zA-Z_][a-zA-Z_0-9]*/', $this->arg);
    }

    public function append_space($token)
    {
        if ($this->parent instanceof SQLPairedGroup) {
            $this->arg .= $token;
            return $this;
        }
        return parent::append_space($token);
    }
    public function lower()
    {
        $this->arg = strtolower($this->arg);
        return $this;
    }
}

class SQLUnary extends SQL
{
    public static $input_priority = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public $arg;

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
        $arg->parent = $this;
    }

    public function replace($old, $new)
    {
        assert($this->arg === $old, new Exception("assert failed: public function replace(\$old, \$new)"));
        $this->arg = $new;
        if (!$new->parent)
            $new->parent = $this;
    }

    public function __clone()
    {
        parent::__clone();
        $this->arg = clone $this->arg;
        $this->arg->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        return $this->arg->jsonSerialize();
    }
}

class SQLPairedGroup extends SQLUnary
{
    public function append($new)
    {
        // if ($new == $this::class)
        if ($new == get_class($this))
            return $this;

        if ($new instanceof SQLToken) {
            $this->parent->replace($this, new SQLArgsSpaceSeparated([$this, $new]));
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_comma($caret)
    {
        if ($caret instanceof SQLToken && is_string($caret->arg)) {
            $caret->arg .= ',';
            return $caret;
        }
        if ($caret instanceof SQLCaret) {
            $new = new SQLToken(',');
            $this->replace($caret, $new);
            return $new;
        }
        return parent::insert_comma($caret);
    }

    public function insert_left_parenthesis($caret)
    {
        $word = '(';
        return $caret->append_token($word);
    }

    public function append_right_parenthesis()
    {
        $word = ')';
        return $this->arg->append_token($word);
    }

    public function insert_operator($caret, $token)
    {
        return $caret->append_token($token);
    }

    public function insert_end($caret)
    {
        $word = 'end';
        return $caret->append_token($word);
    }
}

class SQLApostrophe extends SQLPairedGroup
{
    public function __toString()
    {
        return "'$this->arg'";
    }

    public function jsonSerialize(): mixed
    {
        return "'$this->arg'";
    }

    public function insert_apostrophe($caret)
    {
        if ($caret === $this->arg)
            return $this;
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class SQLQuotation extends SQLPairedGroup
{
    public function __toString()
    {
        return "\"$this->arg\"";
    }

    public function jsonSerialize(): mixed
    {
        return "\"$this->arg\"";
    }

    public function insert_apostrophe($caret)
    {
        return $caret->append_token("'");
    }    
}

class SQLGraveAccent extends SQLPairedGroup
{
    public function __toString()
    {
        return "`$this->arg`";
    }

    public function jsonSerialize(): mixed
    {
        return "`$this->arg`";
    }

    public function insert_apostrophe($caret)
    {
        return $caret->append_token("'");
    }
}

class SQLOperator extends SQLUnary
{
    public $func;
    public function __construct($func, $arg, $parent = null)
    {
        parent::__construct($arg, $parent);
        assert(is_string($func), new Exception("assert failed: public function __construct(\$func, \$arg, \$parent = null)"));
        $this->func = strtolower($func);
    }

    public function __toString()
    {
        return "$this->func $this->arg";
    }

    public function jsonSerialize(): mixed
    {
        $func = $this->func;
        switch ($this->func) {
            case 'order by':
                $func = 'order';
        }
        return [$func => $this->arg->jsonSerialize()];
    }
}

class SQLParenthesis extends SQLUnary
{
    public function __construct($arg, $parent = null)
    {
        parent::__construct($arg, $parent);
    }

    public function __toString()
    {
        return "($this->arg)";
    }

    public function append_right_parenthesis()
    {
        return $this;
    }

    public function insert_comma($caret)
    {
        $new = new SQLCaret($this);
        $this->replace($this->arg, new SQLArgsCommaSeparated([$this->arg, $new]));
        return $new;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return -0.5;
            default:
                return parent::__get($vname);
        }
    }
}

abstract class SQLArgs extends SQL
{
    public static $input_priority = 2;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public $args;
    public function insert_desc($caret) {
        $token = "desc";
        return $caret->append_token($token);
    }


    public function __construct($args, $parent = null)
    {
        parent::__construct($parent);
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    public function replace($old, $new)
    {
        $i = std\index($this->args, $old);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        if (is_array($new)) {
            array_splice($this->args, $i, 1, $new);
            foreach ($new as $el) {
                if (!$el->parent)
                    $el->parent = $this;
            }
        } else {
            $this->args[$i] = $new;
            if (!$new->parent)
                $new->parent = $this;
        }
    }

    public function removeChild($node)
    {
        $i = std\index($this->args, $node);
        if ($i < 0)
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        std\array_delete($this->args, $i);

        if (count($this->args) == 1) {
            [$arg] = $this->args;
            $parent = $this->parent;
            $parent->replace($this, $arg);
            $arg->parent = $parent;
        }
    }

    public function jsonSerialize(): mixed
    {
        return array_map(fn($arg) => $arg->jsonSerialize(), $this->args);
    }

    public function push($arg)
    {
        $this->args[] = $arg;
        $arg->parent = $this;
    }
}

class SQLBinary extends SQLArgs
{
    public static $input_priority = 2;

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct([$lhs, $rhs], $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'lhs':
                return $this->args[0];
            case 'rhs':
                return $this->args[1];
            case 'stack_priority':
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'lhs':
                $this->args[0] = $val;
                break;
            case 'rhs':
                $this->args[1] = $val;
                break;
        }
        $val->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        return [$this->func => [$this->lhs->jsonSerialize(), $this->rhs->jsonSerialize()]];
    }
}

class SQLDot extends SQLBinary
{
    public function insert_desc($caret) {
        return $this->parent->insert_desc($this);
    }

    public function __toString()
    {
        return implode(".", array_map(fn($arg) => "$arg", $this->args));
    }

    public function jsonSerialize(): mixed
    {
        return [$this->lhs->jsonSerialize() => $this->rhs->jsonSerialize()];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 6;
            default:
                return parent::__get($vname);
        }
    }
}

class SQLRegexp extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" regexp ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'regexp';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLNotRegexp extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" not regexp ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'not_regexp';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLike extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __toString()
    {
        return implode(" like ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'like';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLNotLike extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __toString()
    {
        return implode(" not like ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'not_like';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLRelational extends SQLBinary
{
    public static $input_priority = 3.2;
}


class SQLGt extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" > ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'gt';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLGe extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" >= ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'ge';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLt extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" < ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'lt';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLe extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" <= ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'le';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLEq extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" = ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'eq';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLNe extends SQLRelational
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" != ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'ne';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLArithmetic extends SQLBinary
{
    public static $input_priority = 4.0;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 3.2;
            default:
                return parent::__get($vname);
        }
    }
}


class SQLAdd extends SQLArithmetic
{
    public static $input_priority = 4.2;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" + ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'add';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLSub extends SQLArithmetic
{
    public static $input_priority = 4.2;
    public function __toString()
    {
        return implode(" - ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'sub';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLMul extends SQLArithmetic
{
    public static $input_priority = 4.5;
    public function __toString()
    {
        return implode(" * ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'mul';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLDiv extends SQLArithmetic
{
    public static $input_priority = 4.5;
    public function __toString()
    {
        return implode(" / ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'div';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLBitAnd extends SQLArithmetic
{
    public static $input_priority = 4.1;
    public function __toString()
    {
        return implode(" & ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'bit_and';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLBitOr extends SQLArithmetic
{
    public function __toString()
    {
        return implode(" | ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'bit_or';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLBitXor extends SQLArithmetic
{
    public function __toString()
    {
        return implode(" ^ ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'bit_xor';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLSHL extends SQLArithmetic
{
    public function __toString()
    {
        return implode(" << ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'shl';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLSHR extends SQLArithmetic
{
    public function __toString()
    {
        return implode(" >> ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'shr';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLMod extends SQLArithmetic
{
    public function __toString()
    {
        return implode(" % ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'mod';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLAs extends SQLBinary
{
    public static $input_priority = 2.8;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" as ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'as';
            default:
                return parent::__get($vname);
        }
    }

    public function insert_comma($caret)
    {
        $self = $this->parent;
        if ($self instanceof SQLSelect) {
            $new = new SQLCaret($self);
            if (std\is_list($self->select)) {
                assert(end($self->select) === $this);
                $self->select[] = $new;
            } else {
                assert($self->select === $this);
                $self->select = [$self->select, $new];
            }
            return $new;
        } elseif ($self instanceof SQLWith) {
            $new = new SQLCaret($self);
            if (std\is_list($self->with)) {
                assert(end($self->with) === $this);
                $self->with[] = $new;
            } else {
                assert($self->with === $this);
                $self->with = [$self->with, $new];
            }
            return $new;
        } else
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class SQLIn extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" in ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'in';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLNotIn extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" not in ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'not_in';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLIs extends SQLBinary
{
    public static $input_priority = 3.5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" is ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'is';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLIsNot extends SQLBinary
{
    public static $input_priority = 3.5;

    public function __toString()
    {
        return implode(" is not ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'is_not';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLUnion extends SQLBinary
{
    public static $input_priority = 0;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" union ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'union';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLUnionAll extends SQLBinary
{
    public static $input_priority = 0;
    public function __toString()
    {
        return implode(" union all ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'union_all';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLAbstractJoin extends SQLBinary
{
    public static $input_priority = 0.9;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 0.9;
            default:
                return parent::__get($vname);
        }
    }
}


class SQLInnerJoin extends SQLAbstractJoin
{
    public $using;
    public $on;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
        $this->using = null;
        $this->on = null;
    }

    public function __toString()
    {
        $tables = implode(" join ", array_map(fn($arg) => "$arg", $this->args));
        if ($this->using) {
            return "$tables using $this->using";
        } elseif ($this->on) {
            return "$tables on $this->on";
        } else
            return $tables;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'join';
            default:
                return parent::__get($vname);
        }
    }

    public function append_using()
    {
        $using = new SQLCaret();
        $this->using = $using;
        $using->parent = $this;
        return $using;
    }
    public function append_on()
    {
        $on = new SQLCaret();
        $this->on = $on;
        $on->parent = $this;
        return $on;
    }

    public function replace($old, $new)
    {
        if ($this->using === $old)
            $this->using = $new;
        elseif ($this->on === $old)
            $this->on = $new;
        else {
            parent::replace($old, $new);
            return;
        }
        if (!$new->parent)
            $new->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        $dict = parent::jsonSerialize();
        if ($this->using) {
            $dict['using'] = $this->using->jsonSerialize();
        } elseif ($this->on) {
            $dict['on'] = $this->on->jsonSerialize();
        }
        return $dict;
    }
}

// typdef SQLInnerJoin SQLJoin;
class_alias("SQLInnerJoin", "SQLJoin");

class SQLCrossJoin extends SQLAbstractJoin
{
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" cross join ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'cross_join';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLLeftJoin extends SQLAbstractJoin
{

    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" left join ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'left_join';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLRightJoin extends SQLAbstractJoin
{
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" right join ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'right_join';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLFullJoin extends SQLAbstractJoin
{
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" full join ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'full_join';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLJsonExtract extends SQLBinary
{
    public static $input_priority = 5;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode('->', array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 4.5;
            case 'func':
                return 'json_extract';
            default:
                return parent::__get($vname);
        }
    }
}


class SQLJsonExtractUnquote extends SQLJsonExtract
{
    public function __toString()
    {
        return implode('->>', array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'func':
                return 'json_extract_unquote';
            default:
                return parent::__get($vname);
        }
    }
}

class SQLLogical extends SQLBinary {}


class SQLAnd extends SQLLogical
{
    public static $input_priority = 1;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" and ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 3;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof SQLAnd) {
            return ['and' => [...$lhs['and'], $rhs]];
        }

        return ['and' => [$lhs, $rhs]];
    }
}


class SQLOr extends SQLLogical
{
    public static $input_priority = 1;
    public function __construct($lhs, $rhs, $parent = null)
    {
        parent::__construct($lhs, $rhs, $parent);
    }

    public function __toString()
    {
        return implode(" or ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 0.9;
            default:
                return parent::__get($vname);
        }
    }

    public function jsonSerialize(): mixed
    {
        $lhs = $this->lhs->jsonSerialize();
        $rhs = $this->rhs->jsonSerialize();
        if ($this->lhs instanceof SQLOr) {
            return ['or' => [...$lhs['or'], $rhs]];
        }

        return ['or' => [$lhs, $rhs]];
    }
}

class SQLFunction extends SQLArgs
{
    public function __construct($func, ...$args)
    {
        parent::__construct([$func->lower(), ...$args]);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 2.79;
            case 'func':
                return $this->args[0];
            case 'parameters':
                return array_slice($this->args, 1);
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        $args = implode(", ", array_map(fn($arg) => "$arg", $this->parameters));
        return "$this->func($args)";
    }

    public function jsonSerialize(): mixed
    {
        $parameters = $this->parameters;
        if (count($parameters) == 1 && $parameters[0] instanceof SQLCaret) {
            $parameters = [];
        }
        return ["$this->func" => array_map(fn($arg) => $arg->jsonSerialize(), $parameters)];
    }

    public function insert_comma($caret)
    {
        $new = new SQLCaret($this);
        $this->args[] = $new;
        return $new;
    }

    public function append_right_parenthesis()
    {
        return $this;
    }

    public function insert_order($caret)
    {
        return $this->insert_operator($caret, 'order by');
    }

    public function insert_operator($caret, $func)
    {
        $new = new SQLCaret();
        $index = count($this->args) - 1;
        $this->args[$index] = new SQLArgsSpaceSeparated([$this->args[$index], new SQLOperator($func, $new)], $this);
        return $new;
    }
}

class SQLArgsSpaceSeparated extends SQLArgs
{
    public static $input_priority = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public function append($new)
    {
        if ($new instanceof SQLToken) {
            $this->args[] = $new;
            $new->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __toString()
    {
        return implode(" ", array_map(fn($arg) => "$arg", $this->args));
    }

    public function insert_operator($caret, $func)
    {
        $new = new SQLCaret();
        $this->args[] = new SQLOperator($func, $new, $this);
        return $new;
    }
}

class SQLArgsCommaSeparated extends SQLArgs
{
    public static $input_priority = 2;

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 2;
            default:
                return parent::__get($vname);
        }
    }

    public function append($new)
    {
        if ($new instanceof SQLToken) {
            $this->args[] = $new;
            $new->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __toString()
    {
        return implode(",", array_map(fn($arg) => "$arg", $this->args));
    }

    public function insert_operator($caret, $func)
    {
        $new = new SQLCaret();
        $this->args[] = new SQLOperator($func, $new, $this);
        return $new;
    }
}

class SQLCase extends SQLArgs
{
    public static $input_priority = 2;

    public function __construct($arg, $parent = null)
    {
        parent::__construct([$arg], $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_priority":
                return 0;
            default:
                return parent::__get($vname);
        }
    }

    public function append($new)
    {
        if ($new instanceof SQLToken) {
            $this->args[] = $new;
            $new->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __toString()
    {
        return "case " . implode("\n", array_map(fn($arg) => "$arg", $this->args)) . " end";
    }

    public function jsonSerialize(): mixed
    {
        return ["case" => array_map(fn($arg) => $arg->jsonSerialize(), $this->args)];
    }

    public function insert_when($caret)
    {
        if (!($caret instanceof SQLCaret)) {
            $caret = new SQLCaret();
            $this->push($caret);
        }
        return $caret->push_when();
    }

    public function insert_end($caret)
    {
        return $this;
    }
}

class SQLWhen extends SQLArgs
{
    public static $input_priority = 2;
    public function __construct($arg, $parent = null)
    {
        parent::__construct([$arg], $parent);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "stack_priority":
                return 0;
            case "when":
                return $this->args[0];
            case "then":
                return $this->args[1] ?? null;

            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case "when":
                $this->args[0] = $val;
                break;
            case "then":
                $this->args[1] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }

    public function append($new)
    {
        if ($new instanceof SQLToken) {
            $this->args[] = $new;
            $new->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __toString()
    {
        return "when $this->when then $this->then";
    }

    public function jsonSerialize(): mixed
    {
        return ["when" => $this->when->jsonSerialize(), "then" => $this->then->jsonSerialize()];
    }

    public function insert_then($caret)
    {
        if ($this->then == null) {
            $caret = new SQLCaret();
            $this->then = $caret;
            return $caret;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}

class SQLSentence extends SQLArgs
{

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return -1;
            case 'root':
                return $this;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return implode(";\n", array_map(fn($arg) => "$arg", $this->args));
    }

    public function append_semicolon()
    {
        $caret = new SQLCaret($this);
        $this->args[] = $caret;
        return $caret;
    }

    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof SQLCaret)
            array_pop($args);
        if (count($args) == 1)
            [$args] = $args;
        return $args;
    }
}


class SQLStatement extends SQLArgs
{
    public function __construct($from = null, $where = null, $group = null, $having = null, $order = null, $limit = null, $offset = null, $parent = null)
    {
        parent::__construct([], $parent);
        if ($from)
            $this->from = $from;
        if ($where)
            $this->where = $where;
        if ($group)
            $this->group = $group;
        if ($having)
            $this->having = $having;
        if ($order)
            $this->order = $order;
        if ($limit)
            $this->limit = $limit;
        if ($offset)
            $this->offset = $offset;
    }

    public function replace($old, $new)
    {
        if ($this->from === $old)
            $this->from = $new;
        elseif ($this->where === $old)
            $this->where = $new;
        elseif ($this->order === $old)
            $this->order = $new;
        elseif ($this->limit === $old)
            $this->limit = $new;
        elseif ($this->offset === $old)
            $this->offset = $new;
        elseif ($this->group === $old)
            $this->group = $new;
        elseif ($this->having === $old)
            $this->having = $new;
        else
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));

        if (!$new->parent)
            $new->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        return [
            'where' => $this->where ? $this->where->jsonSerialize() : null,
            'from' => $this->from->jsonSerialize(),
            'group' => $this->group ? $this->group->jsonSerialize() : null,
            'having' => $this->having ? $this->having->jsonSerialize() : null,
            'order' => $this->order ? $this->order->jsonSerialize() : null,
            'limit' => $this->limit ? $this->limit->jsonSerialize() : null,
            'offset' => $this->offset ? $this->offset->jsonSerialize() : null,
        ];
    }

    public function append_where()
    {
        if (!$this->where) {
            $this->where = new SQLCaret($this);
            return $this->where;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_group($caret)
    {
        if (!$this->group) {
            $this->group = new SQLCaret($this);
            return $this->group;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_having()
    {
        if (!$this->having) {
            $this->having = new SQLCaret($this);
            return $this->having;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_order($caret)
    {
        if (!$this->order) {
            $this->order = new SQLCaret($this);
            return $this->order;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_limit()
    {
        if (!$this->limit) {
            $this->limit = new SQLCaret($this);
            return $this->limit;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function append_offset()
    {
        if (!$this->offset) {
            $this->offset = new SQLCaret($this);
            return $this->offset;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function toString($sql)
    {
        if ($where = $this->where)
            $sql .= " where $where";

        if ($group = $this->group)
            $sql .= " group by $group";

        if ($having = $this->having)
            $sql .= " having $having";

        if ($order = $this->order)
            $sql .= " order by $order";

        if ($limit = $this->limit) {
            $sql .= " limit $limit";

            if ($offset = $this->offset)
                $sql .= " offset $offset";
        }

        return $sql;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 0;
            case 'from':
                return $this->args[0]?? null;
            case 'where':
                return $this->args[1]?? null;
            case 'group':
                return $this->args[2]?? null;
            case 'having':
                return $this->args[3]?? null;
            case 'order':
                return $this->args[4]?? null;
            case 'limit':
                return $this->args[5]?? null;
            case 'offset':
                return $this->args[6]?? null;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val)
    {
        switch ($vname) {
            case 'from':
                $this->args[0] = $val;
                break;
            case 'where':
                $this->args[1] = $val;
                break;
            case 'group':
                $this->args[2] = $val;
                break;
            case 'having':
                $this->args[3] = $val;
                break;
            case 'order':
                $this->args[4] = $val;
                break;
            case 'limit':
                $this->args[5] = $val;
                break;
            case 'offset':
                $this->args[6] = $val;
                break;
            default:
                throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        }
        $val->parent = $this;
    }
}

class SQLSelect extends SQLStatement
{
    public $select;
    public function __construct($select, $from = null, $where = null, $group = null, $having = null, $order = null, $limit = null, $offset = null, $parent = null)
    {
        parent::__construct($from, $where, $group, $having, $order, $limit, $offset, $parent);
        $this->select = $select;
        $select->parent = $this;
    }

    public function __toString()
    {
        $select = $this->select;
        if (std\is_list($select))
            $select = implode(', ', array_map(fn($arg) => "$arg", $select));

        return $this->toString("select $select from $this->from");
    }

    public function replace($old, $new)
    {
        if (!$this->replace_args($this->select, $old, $new))
            parent::replace($old, $new);
    }

    public function jsonSerialize(): mixed
    {
        $dict = parent::jsonSerialize();
        $select = $this->select;
        $dict['select'] = std\is_list($select) ?
            array_map(fn($arg) => $arg->jsonSerialize(), $select) :
            $select->jsonSerialize();
        return $dict;
    }

    public function append_from()
    {
        if (!$this->from) {
            $this->from = new SQLCaret($this);
            return $this->from;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_comma($caret)
    {
        if (!$this->from) {
            $new = new SQLCaret($this);
            if (std\is_list($this->select))
                $this->select[] = $new;
            else
                $this->select = [$this->select, $new];
            return $new;
        }
    }

    public function insert_operator($caret, $func)
    {
        assert($func == "distinct", '$func == "distinct"');
        if ($this->select instanceof SQLCaret) {
            $new = $this->select;
            $this->select = new SQLOperator($func, $new, $this);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_desc($caret) {
        if ($caret === $this->order) {
            $new = new SQLToken('desc');
            $this->order = new SQLArgsSpaceSeparated([$caret, $new]);
            return $new;
        }
        return $this->parent->insert_desc($this);
    }
}

class SQLDelete extends SQLStatement
{
    public function append_from()
    {
        if (!$this->from)
            $this->from = new SQLCaret($this);

        if ($this->from instanceof SQLCaret)
            return $this->from;
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function __toString()
    {
        return $this->toString("delete from $this->from");
    }

    public function jsonSerialize(): mixed
    {
        $dict = parent::jsonSerialize();
        $dict['delete'] = true;
        return $dict;
    }
}

class SQLUpdate extends SQLStatement
{
    public $set;
    public function __construct($from = null, $set = null, $where = null, $group = null, $having = null, $order = null, $limit = null, $offset = null, $parent = null)
    {
        parent::__construct($from, $where, $group, $having, $order, $limit, $offset, $parent);
        $this->set = $set;
        // $set->parent = $this;
    }

    public function __toString()
    {
        $set = $this->set;
        if (std\is_list($set))
            $set = implode(', ', array_map(fn($arg) => "$arg", $set));

        return $this->toString("update $this->from set $set");
    }

    public function replace($old, $new)
    {
        if (!$this->replace_args($this->set, $old, $new))
            parent::replace($old, $new);
    }

    public function jsonSerialize(): mixed
    {
        $dict = parent::jsonSerialize();
        $dict['update'] = $dict['from'];
        unset($dict['from']);
        $set = $this->set;
        $dict['set'] = std\is_list($set) ?
            array_map(fn($arg) => $arg->jsonSerialize(), $set) :
            $set->jsonSerialize();
        return $dict;
    }
    public function append_set()
    {
        if (!$this->set)
            $this->set = new SQLCaret($this);

        if ($this->set instanceof SQLCaret)
            return $this->set;
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_comma($caret)
    {
        if (!$this->where) {
            $new = new SQLCaret($this);
            if (std\is_list($this->set))
                $this->set[] = $new;
            else
                $this->set = [$this->set, $new];
            return $new;
        }
    }
}

class SQLWith extends SQL
{
    public $recursive;
    public $with;
    public $sql;
    public function __construct($with, $sql, $parent = null, $recursive = false)
    {
        parent::__construct($parent);
        $this->with = $with;
        $this->sql = $sql;
        $with->parent = $this;
        if ($sql)
            $sql->parent = $this;
        $this->recursive = $recursive;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 0;
            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        $sql = $this->sql;
        $with = $this->with;
        if ($with) {
            if (std\is_list($with))
                $with = implode(', ', array_map(fn($arg) => "$arg", $with));

            $recursive = $this->recursive ? ' recursive' : '';
            $sql = "with$recursive $with $sql";
        }
        return $sql;
    }

    public function replace($old, $new)
    {
        if ($this->replace_args($this->with, $old, $new));
        elseif ($this->sql === $old)
            $this->sql = $new;
        else
            throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
        if (!$new->parent)
            $new->parent = $this;
    }

    public function jsonSerialize(): mixed
    {
        $dict = $this->sql->jsonSerialize();
        $func = 'with';
        if ($this->recursive)
            $func .= '_recursive';
        if (std\is_list($this->with))
            $dict[$func] = array_map(fn($arg) => $arg->jsonSerialize(), $this->with);
        else
            $dict[$func] = $this->with->jsonSerialize();
        return $dict;
    }

    public function append($type)
    {
        if (is_string($type)) {
            $new = new SQLCaret();
            $this->sql = new $type($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
}


function parseSQL($sql)
{
    $expr = SQL::compile($sql);
    $expr->jsonSerialize();
    echo std\encode($expr);
}

//parseSQL();
