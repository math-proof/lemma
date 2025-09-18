<?php
use std\DecoratorAttribute;

abstract class Node implements JsonSerializable {
    public $parent;
    public $args = [];
    protected $kwargs = [];

    public function __construct($kwargs, $parent=null) {
        $this->kwargs = $kwargs;
        $this->parent = $parent;
        $this->args = [];
    }

    public function __get($vname) {
        switch ($vname) {
            case 'indent':
                return $this->kwargs['indent'];
            case 'text':
                return $this->kwargs['text'];
            case 'start_idx':
                return $this->kwargs['start_idx'];
            case 'end_idx':
                return $this->kwargs['end_idx'];
            case 'func':
                return basename(str_replace('\\', '/', get_class($this)));
            case 'root':
                return $this->parent ? $this->parent->root : null;
            case 'bind':
                return [
                    'args' => $this->args,
                    'kwargs' => $this->kwargs
                ];
            }
    }

    public function __set($vname, $val) {
        switch ($vname) {
            case 'indent':
                $this->kwargs['indent'] = $val;
                break;
            case 'text':
                $this->kwargs['text'] = $val;
                break;
            case 'start_idx':
                $this->kwargs['start_idx'] = $val;
                break;
            case 'end_idx':
                $this->kwargs['end_idx'] = $val;
                break;
            }
    }

    public function kwargs_list() {
        return [];
    }

    public function clone() {
        $class = get_class($this);
        $instance = new $class($this->indent, $this->parent);
        $instance->args = $this->args;
        $instance->kwargs = $this->kwargs;
        return $instance;
    }

    public function __toString() {
        $str = $this->strFormat();
        if ($this->args)
            return sprintf($str, ...array_map('strval', $this->args));
        return $str;
    }

    // public function append($newNode) {
    //     if ($this->parent) {
    //         return $this->parent->append($newNode);
    //     }
    //     throw new \Exception("append is not defined for " . $newNode->func . " : " . $this->func);
    // }

    public function jsonSerialize() : mixed {
        return (string)$this;
    }

    public function getPreviousElementSibling() {
        if (!$this->parent) return null;
        $index = array_search($this, $this->parent->args, true);
        return ($index > 0) ? $this->parent->args[$index - 1] : null;
    }

    public function remove() {
        if ($this->parent)
            $this->parent->removeChild($this);
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

    public function removeChild($node, $deleteFlag = null) {
        $i = array_search($node, $this->args, true);
        if ($i === false) {
            error_log("removeChild is unexpected for " . get_class($this));
            return;
        }
        array_splice($this->args, $i, 1);
        if (count($this->args) === 1 && $deleteFlag) {
            $arg = $this->args[0];
            $parent = $this->parent;
            if ($parent) {
                $parent->replace($this, $arg);
                $arg->parent = $parent;
            }
        }
    }

    public function push($arg) {
        $this->args[] = $arg;
        $arg->parent = $this;
    }

    public function unshift($arg) {
        array_unshift($this->args, $arg);
        $arg->parent = $this;
    }

    public function is_indented() {
        return false;
    }

    public function compareTo($index) {
        if ($this->end_idx <= $index->start_idx) return -1;
        if ($this->start_idx >= $index->end_idx) return 1;
        return 0;
    }

    public function parse($text, ...$kwargs) {
        // Late static binding resolves to the inherited class at runtime
        // assert(property_exists(static::class, 'case'));
        if (isset(static::$case[$text])) {
            $fun = static::$case[$text];
            return $this->$fun(...$kwargs);
        }
        return $this->case_default($text, ...$kwargs);
    }

    abstract function case_default($text, ...$kwargs);

    public function dfs() {
        yield $this;
        foreach ($this->args as $arg) {
            yield from $arg->dfs();
        }
    }

    public function bfs() {
        $queue = [$this];
        while (!empty($queue)) {
            $node = array_shift($queue);
            yield $node;
            $queue = array_merge($queue, $node->args);
        }
    }

    protected function strFormat() {
        return '';
    }
}

abstract class AbstractParser {
    public $caret;

    public function __construct($caret) {
        $this->caret = $caret;
    }

    public function parse($token, ...$kwargs) {
        $this->caret = $this->caret->parse($token, ...$kwargs);
        return $this->caret;
    }

    public function __get($vname) {
        switch ($vname) {
            case 'bind':
                return ['root' => $this->caret];
            case 'func':
                $name = basename(str_replace('\\', '/', get_class($this)));
                if (substr($name, -6) === 'Parser')
                    $name = strtolower(substr($name, 0, -6));
                return $name;
        }
    }
}

trait Closable {
    public function __get($vname) {
        switch ($vname) {
            case 'is_closed':
                return $this->kwargs['is_closed'] ?? null;
            default:
                return parent::__get($vname);
        }
    }

    public function __set($vname, $val) {
        switch ($vname) {
            case 'is_closed':
                $this->kwargs['is_closed'] = $val;
                break;
            default:
                parent::__set($vname, $val);
        }
    }
}

abstract class IndentedNode extends Node {
    public function __construct($indent = 0, $parent = null) {
        parent::__construct(['indent' => $indent], $parent);
    }
}


#[Attribute(Attribute::TARGET_METHOD)]
class MatchCase implements DecoratorAttribute {
    public function __construct(private ?string $key = null) {}

    public function getCallback(callable $wrapped, \ReflectionMethod $method): callable {
        return $wrapped;
    }

    public function __init__(string $class, string $method) {
        $class::$case[$this->key] = $method;
    }
}
