<?php
require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/node.php';

class Word extends Node {
    static $ascii = array_merge(array_map('strval', range(0, 9)), ['_'], range('a', 'z'), range('A', 'Z'));

    public function case($key, ...$kwargs): self {
        if (in_array($key, self::$ascii, true)) {
            $this->setText($this->getText() . $key);
            return $this;
        }
        return $this->parent->parse($this->kwargs)->parse($key, ...$kwargs);
    }

    protected function strFormat(): string {
        return $this->getText();
    }
}

class WordParser extends AbstractParser {
    public function __construct($caret, ...$kwargs) {
        parent::__construct(new Word($caret, ...$kwargs));
        $this->caret->setText('');
    }
}