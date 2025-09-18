<?php
require_once __DIR__ . '/unescape.php';

// use the following regex to remove error_log prints:
// ^ *error_log
// javaScript to php transformation:

// ^[ \t]*constructor\(
// \tpublic function __construct\(

// var +

// (?<!(?:->|["'\w.$\\]|(?:get|class|function) ))([a-z_]+\w*)(?![(:])(?<!\b(of|if|return|class|function|null|new|in|ranged?|extends|true|len|instanceof|sum|get|for|enumerate|do|while|else|throw|public|break|case|default|continue|switch))\b
// \$\1

// get (\w+)\(\) *\{
// case "\1":

// ^[ \t]*(\w+)\(((\$\w+(, *\$\w+)*)?)\) *\{ *$
// \tfunction \1(\2) {

// (\w+)\.
// \1->

// \.(\w+)
// ->\1

// if *\((\$\w+) in (\$\w+)\)
// if \(isset\(\2[\1]\)\)

// \{\$\w+(?:, *\$\w+)*\} = ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+);
// extract(\1);

// \{\}
// []

// (\$\w+) *=> *\{
// function\(&\1\) \{

// balancedParentheses:
// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)

// (\$\w+) *=> *((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)(?=[,)])
// fn(&\1) => \2

// \((\$\w+(?:, *\$\w+))+\) *=> *((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)(?=[,)])
// fn(&\1) => \2

// ^([ \t]*)Object(?:->|\.)assign\(\$(\w+), \{\$(\w+), *\$(\w+)\}\) *;
// \1\$\2['\3'] = \$\3;\n\1\$\2['\4'] = \$\4;

// ^([ \t]*)Object(?:->|\.)assign\(\$(\w+), \{\$(\w+), *\$(\w+), *\$(\w+)\}\) *;
// \1\$\2['\3'] = \$\3;\n\1\$\2['\4'] = \$\4;\n\1\$\2['\5'] = \$\5;

// for *\((\$\w+) in (\$\w+)\) *\{
// foreach \(\2 as \1 => &\$value\) \{

// for *\((?:var )?\[(\$\w+), *(\$\w+)\] of Object(?:->|\.)entries\(((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)\) *\) *\{
// foreach \(\3 as \1 => &\2\) \{

// for *\((\$\w+) +of +((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)\)
// foreach \(\2 as &\1\)

// for *\(\[(\$\w+(?:, *\$\w+)+)\] +of +((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)\)
// foreach \(\2 as list\(\1\)\)

// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->join\((\S+)\)
// implode(\2, \1)

// ((?:[^() .]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->map\((fn \(&?\$\w+\) *=> *((?:[^()]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+))\)
// array_map(\2, \1)

// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->pop\(\)
// array_pop(\1)

// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->back\(\)
// end(\1)

// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->length
// count(\1)

// ((?:[^() ]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)->slice\(((?:[^()]|\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))+)\)
// std\\substring(\1, \2)
class XMLNode
{

    public $parent;

    public $_style;

    public $_logicalOffset;

    public $_physicalOffset;

    public $_offset;

    public function __construct($parent = null)
    {
        $this->parent = $parent;
    }

    function append_left_tag($tag)
    {
        $parent = $this->parent;
        $caret = new XMLNodeCaret();
        $node = new XMLNodeContainerTag($tag, $caret, null, $parent);
        if ($parent instanceof XMLNodeArray)
            $parent->args[] = $node;
        else {
            $node = new XMLNodeArray([$this,$node], $parent);
            if ($parent)
                $parent->replace($this, $node);
        }

        return $caret;
    }

    function append_text_node($text)
    {
        $parent = $this->parent;
        $node = new XMLNodeText($text, $parent);
        if ($parent instanceof XMLNodeArray) {

            $parent->args[] = $node;
            return $node;
        } else {
            $array = new XMLNodeArray([$this,$node], $parent);
            if ($parent)
                $parent->replace($this, $array);
            return $array;
        }
    }

    function append_single_tag($tag)
    {
        $parent = $this->parent;
        $node = new XMLNodeVoidTag($tag, $parent);
        if ($parent instanceof XMLNodeArray) {
            $parent->args[] = $node;
            return $node;
        } else {
            $array = new XMLNodeArray([$this,$node], $parent);
            if ($parent)
                $parent->replace($this, $array);
            return $array;
        }
    }

    function modify_style($tag)
    {
        if ($this->text) {
            $set = new std\Range(0, std\len($this->text));
            $this->style;
            $_style = &$this->_style;
            if (isset($_style[$tag]))
                $_style[$tag] = $_style[$tag]->union_without_merging($set);
            else
                $_style[$tag] = $set;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                $self = $this;
                while ($self->parent)
                    $self = $self->parent;
                return $self;

            case 'zeros':
                return [];

            case 'style':
                if ($this->_style === null) {
                    $this->_style = [];
                }

                return $this->_style;

            case 'length':
                return $this->stop - $this->start;

            case 'physicalText':
                return $this->__toString();

            case 'style_input':
                $style_input = array_map(fn ($i) => new std\Set(), std\ranged(std\len($this->text)));

                foreach ($this->style as $tag => $s) {
                    if ($s->is_Range) {
                        foreach (std\range($s->start, $s->stop) as $i) {
                            $style_input[$i]->add($tag);
                        }
                    } elseif ($s->is_Union) {
                        foreach ($s->args as $s) {
                            foreach (std\range($s->start, $s->stop) as $i) {
                                $style_input[$i]->add($tag);
                            }
                        }
                    }
                }

                return $style_input;

            case 'style_traits':
                $style_traits = [];
                foreach ($this->style_input as $s) {
                    $s = [...$s];
                    sort($s);
                    $s = implode('.', $s);
                    $style_traits[] = $s;
                }

                return $style_traits;

            default:
                return null;
        }

        return null;
    }

    function sanctity_check()
    {}

    function interval($className)
    {
        $text = $this->text;
        if ($text) {
            $zeros = $this->zeros;
            if (! count($zeros) || $zeros[0])
                $zeros->unshift(0);

            if (! count($zeros) || end($zeros) < std\len($text))
                $zeros[] = std\len($text);

            return array_map(fn ($i) => ['offsetStart' => $zeros[$i - 1],'offsetStop' => $zeros[$i],'className' => $className], std\ranged(1, count($zeros)));
        } else
            return [];
    }

    function getLogicalIndices(&$segments)
    {
        $logicalOffset = [];
        $start = 0;

        $logicalText = $this->text;
        $totalLength = std\len($logicalText);
        foreach ($segments as $seg) {
            while (std\isspace(std\get($logicalText, $start)))
                ++ $start;

            if (! str_starts_with(std\substring($logicalText, $start), $seg)) {
                $sCumulated = '';
                $hit = false;
                for ($i = $start; $i < $totalLength; ++ $i) {
                    $ch = std\get($logicalText, $i);
                    if (std\isspace($ch))
                        continue;

                    $sCumulated .= $ch;
                    if ($sCumulated == $seg) {
                        $hit = true;
                        break;
                    }
                }

                if ($hit)
                    $seg = std\slice($logicalText, $start, $i + 1);
                else {
                    error_log("\$slice.startsWith(\$seg) failed:");
                    error_log(std\slice($logicalText, $start, $i + 1));
                    error_log($seg);
                    error_log("physical text = $this");
                    error_log(" logical text = $logicalText");
                    error_log('$segments = '.json_encode($segments, true));
                    return;
                }
            }

            $end = $start + std\len($seg);

            $logicalOffset[] = [$start, $end];
            $start = $end;
        }

        return $logicalOffset;
    }
}

class XMLNodeCaret extends XMLNode
{

    public function __construct($parent = null)
    {
        parent::__construct($parent);
    }

    function append_left_tag($tag)
    {
        $caret = new XMLNodeCaret();
        $node = new XMLNodeContainerTag($tag, $caret, null, $this->parent);
        if ($this->parent)
            $this->parent->replace($this, $node);
        return $caret;
    }

    function append_text_node($text)
    {
        $node = new XMLNodeText($text, $this->parent);
        if ($this->parent)
            $this->parent->replace($this, $node);
        return $node;
    }

    function append_single_tag($tag)
    {
        $node = new XMLNodeVoidTag($tag, $this->parent);
        if ($this->parent)
            $this->parent->replace($this, $node);
        return $node;
    }

    public function __toString()
    {
        return "";
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeCaret':
                return true;

            case 'text':
                return '';

            case 'logicalLength':
                return 0;

            case 'texts':
                return [];

            case 'length':
                return 0;

            default:
                parent::__get($vname);
        }

        return null;
    }
}

class XMLNodeText extends XMLNode
{

    public $arg;

    public function __construct($text, $parent)
    {
        parent::__construct($parent);
        $this->arg = $text;
    }

    public function __toString()
    {
        return $this->arg->__toString();
    }

    public function __set($vname, $value)
    {
        switch ($vname) {
            case 'start':
                $this->arg->start = $start;
                break;

            case 'stop':
                $this->arg->stop = $stop;
                break;

            default:
                break;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeText':
                return true;

            case 'start':
                return $this->arg->start;

            case 'stop':
                return $this->arg->stop;

            case 'text':
                return $this->arg->text;

            case 'logicalLength':
                return $this->arg->length;

            case 'texts':
                return [$this->text];

            default:
                return parent::__get($vname);
        }

        return null;
    }

    function logical2physical($pos)
    {
        return $pos;
    }

    function physical2logical($pos)
    {
        return $pos;
    }

    function getPhysicalIndices($start, $stop)
    {
        return [$start,$stop];
    }

    function append_text_node($text)
    {
        $this->stop = $text->stop;
        return $this;
    }
}

class XMLNodeContainerTag extends XMLNode
{

    public $tagBegin;

    public $arg;

    public $tagEnd;

    public function __construct($tagBegin, $arg, $tagEnd, $parent)
    {
        parent::__construct($parent);
        $this->tagBegin = $tagBegin;
        $this->arg = $arg;
        $this->tagEnd = $tagEnd;
        $this->arg->parent = $this;
    }

    public function __toString()
    {
        $s = $this->tagBegin->__toString() . $this->arg->__toString();
        if ($this->is_unbalanced)
            return $s;
        return $s . $this->tagEnd->__toString();
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeContainerTag':
                return true;

            case 'tag':
                return $this->tagBegin->tag;

            case 'start':
                return $this->tagBegin->start;

            case 'stop':
                if ($this->is_unbalanced) {
                    if ($this->arg->is_XMLNodeCaret)
                        return $this->tagBegin->stop;
                    return $this->arg->stop;
                }

                return $this->tagEnd->stop;

            case 'text':
                return $this->arg->text;

            case 'logicalLength':
                return $this->arg->logicalLength;

            case 'texts':
                return $this->arg->texts;

            case 'zeros':
                return $this->text ? $this->arg->zeros : [0];

            case 'style':
                if ($this->_style === null) {
                    $_style = [];
                    if ($this->text) {
                        if ($this->arg->is_XMLNodeArray) {
                            $args = $this->arg->args;
                            switch ($this->tag) {
                                case 'msub':
                                case 'munder':
                                    if (count($args) == 2)
                                        $args[1]->modify_style('sub');
                                    break;
                                case 'msup':
                                case 'mover':
                                    if (count($args) == 2)
                                        $args[1]->modify_style('sup');
                                    break;
                                case 'msubsup':
                                case 'munderover':
                                    if (count($args) == 3) {
                                        $args[1]->modify_style('sub');
                                        $args[2]->modify_style('sup');
                                    }
                                    break;
                            }
                        }

                        $_style[$this->tag] = new std\Range(0, std\len($this->text));
                        if ($this->arg->style) {
                            foreach ($this->arg->style as $tag => &$set) {
                                if (isset($_style[$tag]))
                                    $_style[$tag] = $_style[$tag]->union_without_merging($set);
                                else
                                    $_style[$tag] = $set;
                            }
                        }
                    }

                    $this->_style = $_style;
                }

                return $this->_style;

            case 'is_unbalanced':
                return ! $this->tagEnd || $this->tagEnd->is_XMLNodeUnbalancedTag;

            default:
                return parent::__get($vname);
        }
    }

    function logical2physical($pos)
    {
        return $this->arg->logical2physical($pos) + $this->tagBegin->length;
    }

    function physical2logical($pos)
    {
        return ($this->arg->physical2logical($pos) - $this->tagBegin->length)->clip(0, len($this->text) - 1);
    }

    function getPhysicalIndices($start, $stop)
    {
        [$start,$stop] = $this->arg->getPhysicalIndices($start, $stop);
        $physicalText = $this->arg->__toString();

        $_stop = $stop;

        while ($physicalText[$_stop] && std\isspace($physicalText[$_stop]))
            ++ $_stop;

        if ($_stop == std\len($physicalText)) {
            $_stop += $this->tagEnd->length;
            if (! $start)
                $stop = $_stop;
        }

        $stop += $this->tagBegin->length;
        if ($start)
            $start += $this->tagBegin->length;

        return [$start,$stop];
    }

    function replace($old, $node)
    {
        if ($this->arg != $old)
            throw new Exception("$arg != $old");
        $this->arg = $node;

        if (! $node->is_XMLNodeCaret) {
            if (! $this->is_unbalanced) {
                // $console->assert($node->stop == $this->tagEnd->start, "$node->stop == $this->tagEnd->start");
            }
        }

        if ($node->parent) {
            // $console->assert($node->parent == $this, "$node->parent == $this");
        } else
            $node->parent = $this;
    }

    function reduceToNodeText()
    {
        $arg = $this->arg;
        $tagBegin = $this->tagBegin;
        $tagEnd = $this->tagEnd;
        $parent = $this->parent;

        // $console->assert($tagEnd == null, "$tagEnd == null");
        if ($parent->is_XMLNodeArray) {
            $index = std\indexOf($parent->args, $this);
            $count = 1;
            $args = null;
            if ($arg->is_XMLNodeArray) {
                $args = $arg->args;
                foreach ($args as &$arg)
                    $arg->parent = $parent;

                if ($args[0]->is_XMLNodeText)
                    $args[0]->start = $tagBegin->start;
                else
                    $args->unshift(new XMLNodeText($tagBegin->reduceToNodeText(), $parent));

                if ($index && $parent->args[$index - 1]->is_XMLNodeText) {
                    -- $index;
                    ++ $count;
                    $args[0]->start = $parent->args[$index]->start;
                }
            } elseif ($arg->is_XMLNodeCaret) {
                $arg = new XMLNodeText($this->tagBegin->reduceToNodeText(), $parent);
                if ($parent->args[$index + 1] && $parent->args[$index + 1]->is_XMLNodeText) {
                    ++ $count;
                    $arg->stop = $parent->args[$index + 1]->stop;
                }

                if ($index && $parent->args[$index - 1]->is_XMLNodeText) {
                    -- $index;
                    ++ $count;
                    $arg->start = $parent->args[$index]->start;
                }

                $args = [$arg];
            } else {
                $arg->parent = $parent;
                if ($arg->is_XMLNodeText) {
                    if ($parent->args[$index + 1] && $parent->args[$index + 1]->is_XMLNodeText) {
                        ++ $count;
                        $arg->stop = $parent->args[$index + 1]->stop;
                    }

                    if ($index && $parent->args[$index - 1]->is_XMLNodeText) {
                        -- $index;
                        ++ $count;
                        $arg->start = $parent->args[$index]->start;
                    } else
                        $arg->start = $tagBegin->start;

                    $args = [$arg];
                } else {
                    $args = [new XMLNodeText($this->tagBegin->reduceToNodeText(), $parent),$arg];
                    if ($index && $parent->args[$index - 1]->is_XMLNodeText) {
                        -- $index;
                        ++ $count;
                        $args[0]->start = $parent->args[$index]->start;
                    }
                }
            }

            $parent->args->splice($index, $count, ...$args);
        } else {
            // $console->assert($parent->is_XMLNodeContainerTag, "$parent->is_XMLNodeContainerTag");
            if ($arg->is_XMLNodeArray) {
                $args = $arg->args;
                if ($args[0]->is_XMLNodeText)
                    $args[0]->start = $tagBegin->start;
                else
                    $args->unshift(new XMLNodeText($tagBegin->reduceToNodeText(), $arg));
            } elseif ($arg->is_XMLNodeText)
                $arg->start = $tagBegin->start;
            elseif ($arg->is_XMLNodeCaret)
                $arg = new XMLNodeText($tagBegin->reduceToNodeText());
            else
                $arg = new XMLNodeArray([new XMLNodeText($this->tagBegin->reduceToNodeText()),$arg]);

            $arg->parent = $parent;
            $parent->replace($this, $arg);
        }
    }

    function append_tag($node)
    {
        $parent = $this->parent;
        if ($parent instanceof XMLNodeArray) {
            $node->parent = $parent;
            // $console->assert(! $node->is_XMLNodeCaret, "!$node->is_XMLNodeCaret");
            $parent->args[] = $node;
            return $node;
        } else {
            $array = new XMLNodeArray([$this,$node], $parent);
            if ($parent)
                $parent->replace($this, $array);
            return $array;
        }
    }

    function sanctity_check()
    {
        $tagBegin = $this->tagBegin;
        $arg = $this->arg;
        $tagEnd = $this->tagEnd;

        if ($this->is_unbalanced) {
            if (! $arg->is_XMLNodeCaret) {
                if ($tagBegin->stop != $arg->start)
                    return "$tagBegin->stop != $arg->start";
            }
        } else {
            if ($arg->is_XMLNodeCaret) {
                if ($tagBegin->stop != $tagEnd->start)
                    return "$tagBegin->stop != $tagEnd->start";
            } else {
                if ($tagBegin->stop != $arg->start)
                    return "$tagBegin->stop != $arg->start";

                if ($arg->stop != $tagEnd->start)
                    return "$arg->stop != $tagEnd->start";
            }
        }

        return $arg->sanctity_check();
    }
}

class XMLNodeVoidTag extends XMLNode
{

    public function __construct($arg, $parent = null)
    {
        parent::__construct($parent);
        $this->arg = $arg;
    }

    public function __toString()
    {
        return $this->arg->__toString();
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeVoidTag':
                return true;

            case 'tag':
                return $this->arg->tag;

            case 'start':
                return $this->arg->start;

            case 'stop':
                return $this->arg->stop;

            case 'text':
                return $this->arg->text;

            case 'logicalLength':
                return 1;

            case 'texts':
                return [$this->text];

            case 'style':
                if ($this->_style === null) {
                    $_style = [];
                    $_style[$this->tag] = new std\Range(0, std\len($this->text));
                    $this->_style = $_style;
                }

                return $this->_style;

            default:
                return parent::__get($vname);
        }

        return null;
    }

    function logical2physical($pos)
    {
        return $this->arg->length - 2;
    }

    function physical2logical($pos)
    {
        return 0;
    }

    function getPhysicalIndices($start, $stop)
    {
        return [0,$this->arg->length];
    }
}

class XMLNodeArray extends XMLNode
{

    public function __construct($args, $parent)
    {
        parent::__construct($parent);
        $this->args = $args;
        foreach ($args as &$ptr)
            $ptr->parent = $this;
    }

    function append_left_tag($tag)
    {
        $caret = new XMLNodeCaret();
        $this->args[] = new XMLNodeContainerTag($tag, $caret, null, $this);
        return $caret;
    }

    function append_text_node($text)
    {
        $node = new XMLNodeText($text, $this);
        // $console->assert(! end($this->args)->is_XMLNodeText, end("!$this->args)->is_XMLNodeText");
        $this->args[] = $node;
        return $node;
    }

    function append_single_tag($tag)
    {
        $node = new XMLNodeVoidTag($tag, $this);
        $this->args[] = $node;
        return $node;
    }

    function append_tag($node)
    {
        $node->parent = $this;
        // $console->assert(! $node->is_XMLNodeCaret, "!$node->is_XMLNodeCaret");
        $this->args[] = $node;
        return $node;
    }

    public function __toString()
    {
        return implode('', array_map(fn (&$el) => $el->__toString(), $this->args));
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeArray':
                return true;

            case 'start':
                return $this->args[0]->start;

            case 'stop':
                return end($this->args)->stop;

            case 'text':
                return implode('', array_map(fn (&$el) => $el->text, $this->args));

            case 'logicalLength':
                return array_sum(array_map(fn (&$el) => $el->logicalLength, $this->args));

            case 'texts':
                $texts = [];
                foreach ($this->args as &$arg) {
                    array_push($texts, ...$arg->texts);
                }
                return $texts;

            case 'zeros':
                $zeros = [];
                $length = 0;
                foreach ($this->args as &$arg) {
                    array_push($zeros, ...array_map(fn (&$zero) => $zero + $length, $arg->zeros));
                    $length += std\len($arg->text);
                }
                return $zeros;

            case 'style':
                if ($this->_style === null) {
                    foreach (std\enumerate($this->args) as [$i,$tagEnd]) {
                        if ($tagEnd->is_XMLNodeUnbalancedTag) {
                            $self = $tagEnd->binaryTag;
                            // $console->assert($self->tagEnd === $tagEnd, "$self->tagEnd === $tagEnd");
                            do {
                                $parent = $self->parent;
                                if ($parent->is_XMLNodeArray) {
                                    $index = std\indexOf($parent->args, $self);
                                    foreach (std\range($index + 1, $parent !== $this ? count($parent->args) : $i) as $j) {
                                        $parent->args[$j]->modify_style($tagEnd->tag);
                                    }
                                }
                                $self = $parent;
                            } while ($parent !== $this);
                        }
                    }

                    $_style = [];
                    $length = 0;
                    foreach ($this->args as &$arg) {
                        if ($arg->style) {
                            foreach ($arg->style as $tag => &$set) {
                                $set = $set->add($length);
                                if (isset($_style[$tag]))
                                    $_style[$tag] = $_style[$tag]->union_without_merging($set);
                                else
                                    $_style[$tag] = $set;
                            }
                        }
                        $length += std\len($arg->text);
                    }

                    $this->_style = $_style;
                }

                return $this->_style;

            case 'logicalOffset':
                if ($this->_logicalOffset === null) {
                    $logicalOffset = [];
                    $start = 0;
                    foreach ($this->args as &$arg) {
                        $stop = $start + $arg->logicalLength;
                        $logicalOffset[] = [$start,$stop];
                        $start = $stop;
                    }

                    $this->_logicalOffset = $logicalOffset;
                }

                return $this->_logicalOffset;

            case 'physicalOffset':
                if ($this->_physicalOffset === null) {
                    $physicalOffset = [];
                    $start = 0;
                    foreach ($this->args as &$arg) {
                        $stop = $start + $arg->length;
                        $physicalOffset[] = [$start,$stop];
                        $start = $stop;
                    }

                    $this->_physicalOffset = $physicalOffset;
                }
                return $this->_physicalOffset;

            case 'offsets':
                if ($this->_offsets === null) {
                    $offsets = [];
                    $offset = 0;
                    foreach ($this->args as &$arg) {
                        $offsets[] = $offset;
                        $offset += $arg->length - $arg->logicalLength;
                    }
                    $this->_offsets = $offsets;
                }

                return $this->_offsets;
            default:
                return parent::__get($vname);
        }

        return null;
    }

    function replace($old, $node)
    {
        $i = std\indexOf($this->args, $old);
        if ($i < 0)
            throw new Error("replace($old, $node)");

        // $console->assert(! $node->is_XMLNodeCaret, "!$node->is_XMLNodeCaret");
        $this->args[$i] = $node;
        if ($i) {
            // $console->assert($this->args[$i - 1]->stop == $node->start, "$this->args[$i - 1]->stop == $node->start");
            if ($node->is_XMLNodeText) {
                // $console->assert(! $this->args[$i - 1]->is_XMLNodeText, "!$this->args[$i - 1]->is_XMLNodeText");
            }
        }

        if ($this->args[$i + 1]) {
            // $console->assert($this->args[$i + 1]->start == $node->stop, "$this->args[$i + 1]->start == $node->stop");
            if ($node->is_XMLNodeText) {
                // $console->assert(! $this->args[$i + 1]->is_XMLNodeText, "!$this->args[$i + 1]->is_XMLNodeText");
            }
        }

        if ($node->parent) {
            // $console->assert($node->parent == $this, "$node->parent == $this");
        } else
            $node->parent = $this;
    }

    function logical2physical($pos)
    {
        $logicalOffset = $this->logicalOffset;
        $offsets = $this->offsets;

        $index = std\binary_search($logicalOffset, $pos, fn ($args, $hit) => $hit >= $args[1] ? - 1 : ($hit < $args[0] ? 1 : 0));
        $prev_start = $logicalOffset[$index][0];
        return $this->args[$index]->logical2physical($pos - $prev_start) + $prev_start + $offsets[$index];
    }

    function physical2logical($pos)
    {
        $logicalOffset = $this->logicalOffset;
        $offsets = $this->offsets;

        $index = std\binary_search($physicalOffset, $pos, fn ($args, $hit) => $hit >= $args[1] ? - 1 : ($hit < $args[0] ? 1 : 0));
        $prev_start = $physicalOffset[$index][0];
        return $this->args[$index]->physical2logical($pos - $prev_start) + $prev_start - $offsets[$index];
    }

    static function cmp($args, $hit)
    {
        return $hit >= $args[1] ? - 1 : ($hit < $args[0] ? 1 : 0);
    }

    function getPhysicalIndices($start, $stop)
    {
        $logicalOffset = $this->logicalOffset;
        $offsets = $this->offsets;

        $index = std\binary_search($logicalOffset, $start, "XMLNodeArray::cmp");
        $_stop = $stop - 1;
        $_index = std\binary_search($logicalOffset, $_stop, "XMLNodeArray::cmp");

        if ($index == $_index) {
            $prev_start = $logicalOffset[$index][0];
            return std\add($this->args[$index]->getPhysicalIndices($start - $prev_start, $stop - $prev_start), $prev_start + $offsets[$index]);
        } else {
            [$prev_start,$prev_stop] = $logicalOffset[$index];
            $_prev_start = $logicalOffset[$_index][0];
            $start = std\add($this->args[$index]->getPhysicalIndices($start - $prev_start, $prev_stop - $prev_start), $prev_start + $offsets[$index])[0];
            $stop = std\add($this->args[$_index]->getPhysicalIndices(0, $stop - $_prev_start), $_prev_start + $offsets[$_index])[1];
            return [$start,$stop];
        }
    }
}

class XMLNodeUnbalancedTag extends XMLNode
{

    public function __construct($tagEnd, $binaryTag, $parent = null)
    {
        parent::__construct($parent);
        $this->tagEnd = $tagEnd;
        $this->binaryTag = $binaryTag;
        $binaryTag->tagEnd = $this;
    }

    public function __toString()
    {
        return $this->tagEnd->__toString();
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_XMLNodeUnbalancedTag':
                return true;

            case 'tag':
                return $this->tagEnd->tag;

            case 'start':
                return $this->tagEnd->start;

            case 'stop':
                return $this->tagEnd->stop;

            case 'text':
                return '';

            case 'logicalLength':
                return 0;

            case 'texts':
                return [];

            case 'zeros':
                return [0];
            default:
                return parent::__get($vname);
        }
    }
}

// /////////RichText->php////////////////////
function compile($infix)
{
    $caret = new XMLNodeCaret();

    $leftTagCount = [];
    foreach ($infix as &$text) {
        if ($text->is_TagBegin) {
            $caret = $caret->append_left_tag($text);

            if (! $leftTagCount[$text->tag])
                $leftTagCount[$text->tag] = [];
            $leftTagCount[$text->tag][] = $caret->parent;
        } elseif ($text->is_TagEnd) {
            $old = $caret;
            while (true) {
                if ($caret) {
                    $root = $caret;
                    $caret = $caret->parent;
                    if ($caret instanceof XMLNodeContainerTag && $caret->tag == $text->tag) {
                        $caret->tagEnd = $text;
                        while (true) {
                            $_caret = array_pop($leftTagCount[$text->tag]);
                            if ($caret === $_caret)
                                break;
                            $_caret->reduceToNodeText();
                        }
                        break;
                    }
                } elseif (count($leftTagCount[$text->tag])) {
                    $parent = array_pop($leftTagCount[$text->tag]);
                    $caret = new XMLNodeUnbalancedTag($text, $parent);
                    while ($parent->stop < $root->stop)
                        $parent = $parent->parent;

                    $caret = $parent->append_tag($caret);
                    break;
                } else {
                    $text = $text->reduceToNodeText();
                    $caret = $old->append_text_node($text);
                    break;
                }
            }
        } elseif ($text->is_VoidTag || $text->is_HTMLEntity)
            $caret = $caret->append_single_tag($text);
        else
            $caret = $caret->append_text_node($text);
    }

    foreach ($leftTagCount as $tag => &$value) {
        while ($value) {
            array_pop($value)->reduceToNodeText();
        }
    }

    return $caret->root;
}

$tagName = '([a-z][-:_a-z]*\d*)';
$attrList = "(?:\s+:?[a-z][-:_a-z]*=(?:\"[^\"]*\"|'[^']*'))*\s*";
$tagBegin = "<$tagName$attrList>";
$tagRegex = "`$tagBegin(?=[\s\S]*?</\\1>)|</$tagName>|<(img|mspace|br)$attrList/>|&(#[0-9]+|#x[0-9a-f]+|[^\t\n\f <&#;]{1,32});`ui";

function construct_rich_text($text)
{
    global $tagRegex;
    $start = 0;

    $richTexts = [];
    $leftTagCount = [];
    foreach (std\matchAll($tagRegex, $text) as [&$m,$index]) {
        // 1-----------------) 2-----------------) 3-------------) 4----------------------------------------)
        $prevText = std\slice($text, $start, $index);
        if (!std\not($prevText)) //$prevText may be '0' which is null!
            $richTexts[] = new PlainText($text, $start, $index);

        $end = $index + std\len($m[0]);
        $richText;
        if ($m[1]) {
            $tag = $m[1];
            $richText = new TagBegin($text, $index, $end, $tag);
            if (! (isset($leftTagCount[$tag])))
                $leftTagCount[$tag] = 0;
            ++ $leftTagCount[$tag];
        } elseif ($m[2]) {
            $tag = $m[2];
            if (std\get($leftTagCount, $tag)) {
                -- $leftTagCount[$tag];
                $richText = new TagEnd($text, $index, $end, $tag);
            } elseif (!std\not($prevText)) { //$prevText may be '0' which is null!
                $richText = array_pop($richTexts);
                $richText->stop = $end;
            } else
                $richText = new PlainText($text, $index, $end);
        } elseif ($m[3])
            $richText = new VoidTag($text, $index, $end, $m[3]);
        else
            $richText = new HTMLEntity($text, $index, $end, $m[4]);

        $richTexts[] = $richText;
        $start = $end;
    }

    $restText = std\slice($text, $start);
    if (!std\not($restText)) //$restText may be '0' which is null!
        $richTexts[] = new PlainText($text, $start, strlen($text));

    return compile($richTexts);
}

class XMLText
{

    public $src;

    public $start;

    public $stop;

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        $this->src = &$src;
        $this->start = $start;
        $this->stop = $stop;
    }

    public function __toString()
    {
        return std\slice($this->src, $this->start, $this->stop);
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'length':
                return $this->stop - $this->start;
            default:
                return null;
        }

        return null;
    }

    function reduceToNodeText()
    {
        return new PlainText($this->src, $this->start, $this->stop);
    }
}

class TagBegin extends XMLText
{

    public $tag;

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        parent::__construct($src, $start, $stop);
        $this->tag = $tag;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_TagBegin':
                return true;
            default:
                return parent::__get($vname);
        }
    }
}

class TagEnd extends XMLText
{

    public $tag;

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        parent::__construct($src, $start, $stop);
        $this->tag = $tag;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_TagEnd':
                return true;
            default:
                return parent::__get($vname);
        }
    }
}

class VoidTag extends XMLText
{

    public $text;

    public $tag;

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        parent::__construct($src, $start, $stop);
        switch (strtolower($tag)) {
            case 'img':
                $text = '★';
                break;
            case 'mspace':
                $text = ' ';
                break;
            case 'br':
                $text = "\n";
                break;
            default:
                $text = '?';
        }

        $this->text = $text;
        $this->tag = $tag;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_VoidTag':
                return true;
            default:
                return parent::__get($vname);
        }
    }
}

class HTMLEntity extends XMLText
{

    public $text;

    public $tag;

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        parent::__construct($src, $start, $stop);
        $text = unescape("&${tag};");

        if (std\len($text) != 1)
            $text = '?';

        $tag = "entity-$tag";
        $this->text = $text;
        $this->tag = $tag;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'is_HTMLEntity':
                return true;
            default:
                return parent::__get($vname);
        }
    }
}

class PlainText extends XMLText
{

    public function __construct(&$src, $start, $stop, $tag = null)
    {
        parent::__construct($src, $start, $stop);
    }

    public function __get($vname)
    {
        switch ($vname) {

            case 'text':
                return std\slice($this->src, $this->start, $this->stop);
            case 'is_PlainText':
                return true;

            default:
                return parent::__get($vname);
        }

        return null;
    }
}

function style_type($ptr, $style)
{
    $offsetStart = $ptr->offsetStart;
    $offsetStop = $ptr->offsetStop;

    $this_set = new std\Range($offsetStart, $offsetStop);
    $style_intersected = [];
    foreach ($style as $tag => &$set) {
        $intersection = $set->intersects($this_set);
        if ($intersection->is_EmptySet)
            continue;

        $style_intersected[$tag] = $intersection;
    }

    if (isEmpty($style_intersected))
        return;

    $indicator = [];
    foreach (std\range($offsetStop - $offsetStart) as &$i) {
        $indicator[$i] = ['className' => $ptr->className];
    }

    function processRangeObject($set, $tag)
    {
        $start = $set->start;
        $stop = $set->stop;

        foreach (std\range($start, $stop) as &$i) {
            $className = $indicator[$i]['className'];
            if ($className)
                $indicator[$i]->className += ' ' + $tag;
            else
                $indicator[$i]->className = $tag;
        }
    }

    foreach ($style_intersected as $tag => &$set) {
        $set = $set->add(- $offsetStart);

        $args = $set->is_Range ? [$set] : $set->args;
        foreach (std\enumerate($args) as [$i,$s]) {
            if ($i && $args[$i - 1]->stop == $s->start)
                $tag = $tag->toggleCase();
            processRangeObject($s, $tag);
        }
    }

    $interval = [];
    $i = 0;
    while ($i < count($indicator)) {
        for ($j = $i + 1; $j < count($indicator); ++ $j) {
            if ($indicator[$j]->className != $indicator[$i]->className)
                break;
        }

        $className = $indicator[$i]->className;
        if (! $className)
            $className = $ptr->className;
        $interval[] = ['offsetStart' => $i + $offsetStart,'offsetStop' => $j + $offsetStart,'className' => $className];
        $i = $j;
    }
    return $interval;
}

function split_interval_by_entity($self, $clazzName, $entity)
{
    $style = [...$self->style];
    foreach ($entity as &$ent) {
        if (! $ent)
            continue;

        $offsetStart = $ent->offsetStart;
        $offsetStop = $ent->offsetStop;
        $className = $ent->className;

        if (! $style[$className])
            $style[$className] = new EmptySet();

        $style[$className] = $style[$className]->union(new std\Range($offsetStart, $offsetStop));
    }

    return detect_style($self->interval($clazzName), $style);
}

function interval($self, $className)
{
    return detect_style($self->interval($className), $self->style);
}

function detect_style($interval, $style)
{
    for ($i = 0; $i < count($interval); ++ $i) {
        $ptr = $interval[$i];

        $stype = style_type($ptr, $style);
        if (is_array($stype)) {
            $interval->splice($i, 1, ...$stype);
            $i += count($stype) - 1;
        } elseif ($stype) {
            $ptr->className += ` ${$stype}`;
        }
    }

    return $interval;
}

?>