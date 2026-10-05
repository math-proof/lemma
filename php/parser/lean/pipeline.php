<?php
/**
 * Pipeline dot `|>.` (`LeanMethodChaining`).
 *
 * Loaded by lean.php after `lazy.php` (`LeanBinary` already exists).
 * Mirrors static/js/parser/lean/pipeline.js. PHP `stack_priority` stays on
 * `__get`. Not a standalone entry point.
 */

class LeanMethodChaining extends LeanBinary
{
    public static $input_priority = 67;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 59;
            default:
                return parent::__get($vname);
        }
    }

    public function latexFormat()
    {
        return '%s\\ \texttt{|>.}%s';
    }
    public function sep()
    {
        return '';
    }

    public function strFormat()
    {
        return '%s |>.%s';
    }
}

// END OF pipeline family (LeanCommand stays in lean.php)
