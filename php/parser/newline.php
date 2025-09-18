<?php
require_once dirname(__file__) . '/node.php';
class NewLine extends IndentedNode
{
    use std\MethodDecorator;
    public $indent = 0;
    public $newline_count = 0;
    public $next = null;
    public $args = [];

    public static $case = [];

    #[MatchCase("\n")]
    public function case_newline(...$kwargs)
    {
        $this->indent = 0;
        $this->newline_count++;
        return $this;
    }

    #[MatchCase(' ')]
    public function case_space(...$kwargs)
    {
        $this->indent++;
        return $this;
    }

    #[MatchCase("\t")]
    public function case_tab(...$kwargs)
    {
        $this->indent += 4;
        return $this;
    }

    public function case_default($key, ...$kwargs)
    {
        $caret = $this->parent;
        $self_kwargs = $this->args;

        if ($this->next)
            array_unshift($self_kwargs, $key);

        return $caret->parent->insert_newline(
            $caret,
            $this->newline_count,
            $this->indent,
            ...$self_kwargs
        )->parse($key, ...$kwargs);
    }
}

// Initialize dispatch map
// NewLine::$case["\n"] = 'case_newline';
// NewLine::$case[" "]  = 'case_space';
// NewLine::$case["\t"] = 'case_tab';

class NewLineParser extends AbstractParser
{
    public function __construct($caret, $next = null, ...$args)
    {
        parent::__construct($caret);
        $this->caret = new NewLine(0, $caret);
        $this->caret->newline_count = 1;
        $this->caret->next = $next;
        $this->caret->args = $args;
    }
}