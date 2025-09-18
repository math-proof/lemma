<?php
require_once dirname(__file__) . '/node.php';
class NewLineSkippingComment extends IndentedNode
{
    use std\MethodDecorator;
    public $indent = 0;
    public $newline_count = 0;
    public $next = null;
    public $args = [];
    public static $case = [];
    public $hyphen_count = 0;
    public $line_comment = [];

    #[MatchCase("\n")]
    public function case_newline(...$kwargs)
    {
        $this->indent = 0;
        if ($this->hyphen_count) {
            assert ($this->hyphen_count >= 2, "Hyphen count must be at least 2 to insert newline");
            $this->line_comment[] = "\n";
            $this->hyphen_count = 0; // Reset hyphen count after newline
        }
        else 
            $this->newline_count++;
        return $this;
    }

    #[MatchCase('-')]
    public function case_hyphen_minus(...$kwargs)
    {
        $this->hyphen_count++;
        $this->line_comment[] = "-";
        return $this;
    }

    #[MatchCase(' ')]
    public function case_space(...$kwargs)
    {
        if ($this->hyphen_count) {
            assert ($this->hyphen_count >= 2, "Hyphen count must be at least 2 to insert space");
            $this->line_comment[] = " ";
        }
        else
            $this->indent++;
        return $this;
    }

    public function case_default($key, ...$kwargs)
    {
        if ($this->hyphen_count) {
            if ($this->hyphen_count >= 2) {
                $this->line_comment[] = $key;
                return $this;
            }
            else {
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
        else {
            $caret = $this->parent;
            $self_kwargs = $this->args;
            if ($this->next)
                array_unshift($self_kwargs, $key);

            $caret = $caret->parent->insert_newline(
                $caret,
                $this->newline_count,
                $this->indent,
                ...$self_kwargs
            );
            if ($this->line_comment) {
                // If there is a line comment, we need to parse it as well
                $self = $kwargs[0];
                $self->caret = $caret;
                $self->start_idx -= $this->indent + count($this->line_comment);
                $start_idx = &$self->start_idx;
                $tokens = &$self->tokens;
                $length = count($self->tokens);
                for (;$start_idx < $length; $start_idx++) {
                    $self->parse($tokens[$start_idx], $self);
                    if (!$self->caret)
                        break;
                }
                return $self->caret;
            }
            return $caret->parse($key, ...$kwargs);
        }
    }
}

// Initialize dispatch map
NewLineSkippingComment::initializeClassDecorators();

class NewLineSkippingCommentParser extends AbstractParser
{
    public function __construct($caret, $next = null, ...$args)
    {
        parent::__construct($caret);
        $this->caret = new NewLineSkippingComment(0, $caret);
        $this->caret->newline_count = 1;
        $this->caret->hyphen_count = 0;
        $this->caret->next = $next;
        $this->caret->args = $args;
    }
}