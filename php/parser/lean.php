<?php
require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/../itertools.php';
require_once dirname(__file__) . '/newline_skipping_comment.php';

ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'LeanAdd',
    '-' => 'LeanSub',
    '*' => 'LeanMul',
    '/' => 'LeanDiv',
    '÷' => 'LeanEDiv',  // euclidean division
    '//' => 'LeanFDiv', // floor division
    '%' => 'LeanModular',
    '×' => 'Lean_times',
    '@' => 'LeanMatMul',
    '•' => 'Lean_bullet',
    '⬝' => 'Lean_cdotp',
    '∘' => 'Lean_circ',
    '▸' => 'Lean_blacktriangleright',
    '⊙' => 'Lean_odot',
    '⊕' => 'Lean_oplus',
    '⊖' => 'Lean_ominus',
    '⊗' => 'Lean_otimes',
    '⊘' => 'Lean_oslash',
    '⊚' => 'Lean_circledcirc',
    '⊛' => 'Lean_circledast',
    '⊜' => 'Lean_circleeq',
    '⊝' => 'Lean_circleddash',
    '⊞' => 'Lean_boxplus',
    '⊟' => 'Lean_boxminus',
    '⊠' => 'Lean_boxtimes',
    '⊡' => 'Lean_dotsquare',
    '∈' => 'Lean_in',
    '∉' => 'Lean_notin',
    '|' => 'LeanBitOr',
    '&' => 'LeanBitAnd',
    '||' => 'LeanLogicOr',
    '|||' => 'LeanBitwiseOr',
    '&&' => 'LeanLogicAnd',
    '&&&' => 'LeanBitwiseAnd',
    '^' => 'LeanPow',
    '^^' => 'LeanLogicXor',
    '^^^' => 'LeanBitwiseXor',
    '<' => 'Lean_lt',
    '<<' => 'Lean_ll',
    '<<<' => 'Lean_lll',
    '<=' => 'Lean_le',
    '>' => 'Lean_gt',
    '>>' => 'Lean_gg',
    '>>>' => 'Lean_ggg',
    '>=' => 'Lean_ge',
    '∨' => 'Lean_lor',
    '∧' => 'Lean_land',
    '∪' => 'Lean_cup',
    '∩' => 'Lean_cap',
    "\\" => 'Lean_setminus',
    '|>.' => 'LeanMethodChaining',
    '<|' => 'Lean_lazy',
    '⊆' => 'Lean_subseteq',
    '⊂' => 'Lean_subset',
    '⊇' => 'Lean_supseteq',
    '⊃' => 'Lean_supset',
    '⊔' => 'Lean_sqcup',
    '⊓' => 'Lean_sqcap',
    '++' => 'LeanAppend',
    '→' => 'Lean_rightarrow',
    '↦' => 'Lean_mapsto',
    '↔' => 'Lean_leftrightarrow',
    '≠' => 'Lean_ne',
    '≡' => 'Lean_equiv',
    '≢' => 'LeanNotEquiv',
    '≍' => 'Lean_asymp',
    '≃' => 'Lean_simeq',
    '≈' => 'Lean_approx',
    '∣' => 'LeanDvd',
];

preg_match_all("/'(\w+)'/", file_get_contents(dirname(__FILE__) . '/../../static/codemirror/mode/lean/tactics.js'), $tactics);
[, $tactics] = $tactics;

require_once dirname(__FILE__) . '/lean/base.php';

require_once dirname(__FILE__) . '/lean/atomic.php';

trait LeanMultipleLine
{
    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line) + 1;
        }
        return $line - 1;
    }
}

require_once dirname(__FILE__) . '/lean/abstract.php';

require_once dirname(__FILE__) . '/lean/paired.php';

require_once dirname(__FILE__) . '/lean/range.php';

require_once dirname(__FILE__) . '/lean/property.php';

require_once dirname(__FILE__) . '/lean/colon.php';

require_once dirname(__FILE__) . '/lean/assign.php';

trait LeanProp
{
    public function isProp($vars)
    {
        return true;
    }
}

require_once dirname(__FILE__) . '/lean/boolean.php';

require_once dirname(__FILE__) . '/lean/relational.php';

require_once dirname(__FILE__) . '/lean/membership.php';

require_once dirname(__FILE__) . '/lean/arithmetic.php';

require_once dirname(__FILE__) . '/lean/lazy.php';

require_once dirname(__FILE__) . '/lean/pipeline.php';

trait LeanGetElemBase
{
    public function push_right($func)
    {
        if ($func == 'LeanBracket')
            return $this;
        return parent::push_right($func);
    }

    public function insert_comma($caret)
    {
        $new = new LeanCaret($this->indent, $caret->level);
        $this->rhs = new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level);
        return $new;
    }
}

trait LeanGetElemBaseBinary 
{
    use LeanGetElemBase;
    public function sep()
    {
        return '';
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 18;
            default:
                return parent::__get($vname);
        }
    }
}


require_once dirname(__FILE__) . '/lean/indexing.php';

require_once dirname(__FILE__) . '/lean/isinstance.php';

require_once dirname(__FILE__) . '/lean/logic.php';

require_once dirname(__FILE__) . '/lean/set.php';

require_once dirname(__FILE__) . '/lean/statements.php';

require_once dirname(__FILE__) . '/lean/module.php';

abstract class LeanCommand extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
        ];
    }
    public function latexFormat()
    {
        return "$this->command %s";
    }
    public function strFormat()
    {
        return "$this->operator %s";
    }

}

class Lean_import extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'import';

            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_open extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'open';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_set_option extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'set_option';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function echo()
    {
        $arg = &$this->arg;
        if ($arg instanceof LeanArgsSpaceSeparated) {
            $args = &$arg->args;
            if (count($args) == 2 && $args[0] instanceof LeanToken && $args[1] instanceof LeanToken) {
                $value = &$args[1]->text;
                if ($args[0]->text == 'maxHeartbeats')
                    $value = strval(intval($value) * 5);
            }
        }
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_namespace extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'namespace';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBar extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                //must be >= LeanAssign::$input_priority
                return LeanAssign::$input_priority;
            case 'operator':
            case 'command':
                return '|';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function is_indented()
    {
        return true;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LeanRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LeanStatements) {
                $arrow->rhs = new LeanCaret($arrow->indent, $arrow->level);
                $stmts->swap_echo_star($syntax, $statements);
            }
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

require_once dirname(__FILE__) . '/lean/arrows.php';

require_once dirname(__FILE__) . '/lean/negation.php';

require_once dirname(__FILE__) . '/lean/match.php';

require_once dirname(__FILE__) . '/lean/ite.php';

require_once dirname(__FILE__) . '/lean/args.php';

require_once dirname(__FILE__) . '/lean/tactic.php';

require_once dirname(__FILE__) . '/lean/decl.php';

require_once dirname(__FILE__) . '/lean/fun.php';

require_once dirname(__FILE__) . '/lean/bigops.php';

require_once dirname(__FILE__) . '/lean/quantifier.php';

function compile($code) {
    return LeanParser::$instance->build($code);
}

class LeanParser extends AbstractParser {
    static $instance = null;
    private $root;
    public $tokens;
    public $start_idx;

    public function __construct() {
    }

    public function __toString() {
        return (string)$this->root;
    }

    public function build($text) {
        $this->init();
        if (!str_ends_with($text, "\n"))
            $text .= "\n";
        $this->tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $text));
        $tokens = &$this->tokens;
        $length = count($tokens);
        $this->start_idx = 0;
        $i = &$this->start_idx;
        for ($i = 0; $i < $length; $i++) {
            $this->parse($tokens[$i], $this);
            if (!$this->caret)
                break;
        }
        return $this->root;
    }
    public function init() {
        $caret = new LeanCaret(0, 0);
        $this->caret = $caret;
        $this->root = new LeanModule([$caret], 0, 0);
    }

}

LeanParser::$instance = new LeanParser();

function escape_specials($token)
{
    return preg_replace_callback(
        '/^(\w+?)_(.+)/',
        function($m) {
            $head = $m[1];
            $tail = preg_replace("/[{}_]/", "\\\\$0", $m[2]);
            return strlen($m[1]) == 1 ? "{$head}_{{$tail}}": "$head\\_$tail";
        },
        $token
    );
}

function latex_tag($tag)
{
    return implode(
        '.',
        array_map(
            fn($tag) => escape_specials($tag),
            explode(".", $tag)
        )
    );
}

function get_lake_path() {
    return std\is_linux() ? "~/.elan/bin/lake": escapeshellcmd(getenv('USERPROFILE') . "\\.elan\\bin\\lake.exe");
}

function get_lean_env()
{
    // add to the file D:\wamp64\bin\apache\apache2.4.54.2\conf\extra\httpd-vhosts.conf
    // SetEnv USERPROFILE "C:\Users\admin" / "C:\Users\Administrator"
    // Configure Git environment variables to trust the directory
    $cwd = getcwd();
    $repository = scandir("$cwd/.lake/packages");
    $repository = array_slice($repository, 2); // Remove . and ..
    $env = [
        'GIT_CONFIG_COUNT' => count($repository),
        // Preserve other important environment variables
        'PATH' => getenv('PATH'),
        // tricks for system profile user on Windows
        // Copy-Item -Path "$HOME\.elan" -Destination "C:\Windows\System32\config\systemprofile\.elan" -Recurse -Force
        'SystemRoot' => getenv('SystemRoot'),
        'HOME' => getenv('HOME')
    ];
    $cwd = str_replace("\\", "/", $cwd);
    foreach ($repository as $index => $directory) {
        $env["GIT_CONFIG_KEY_$index"] = "safe.directory";
        $env["GIT_CONFIG_VALUE_$index"] = "$cwd/.lake/packages/$directory";
    }
    return $env;
}

function transformExpr(string $s0, string $s): string {
    if ($s0 === '_') {
        return $s;
    }
    
    // Check if matches pattern: ^[A-Z][a-zA-Z0-9'!₀-₉]+?S
    if (preg_match('/^[A-Z]$/', $s0)) {
        if (preg_match('/^[a-zA-Z0-9\'!₀-₉]+?S/', $s)) {
            return $s0 . $s;
        }
    }
    
    return '_' . $s0 . $s;
}

function transformPrefix(string $s): string {
    // Pattern 1: EqX, NeX, OrX
    if (preg_match('/^(Eq|Ne|Or)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s2 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s2, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 2: SEqX, HEqX, IffX, AndX
    if (preg_match('/^([SH]Eq)(.)(.*)$/', $s, $matches) || preg_match('/^(Iff|And)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s3 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s3, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 3: LtX, LeX, GtX, GeX (with additional characters)
    if (preg_match('/^(L|G)(t|e)(.)(.*)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $s2 = $matches[3];
        $rest = $matches[4];
        
        // Flip the first character
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        $transformed = transformExpr($s2, $rest);
        return $newS0 . $s1 . $transformed;
    }
    
    // Pattern 3 (short version): Lt, Le, Gt, Ge (no additional characters)
    if (preg_match('/^(L|G)(t|e)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        return $newS0 . $s1;
    }
    
    // If no patterns matched, return original string
    return $s;
}

function is_symm_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne"], true);
}

function is_infix_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne", "lt", "le", "gt", "ge", "in", "ou", "et"], true);
}

function parseInfixSegments(array $list, $section = null): array
{
    if (!$section) {
        $section = $list[0];
        $list = array_slice($list, 1);
    }
    $n = count($list);
    if ($n === 0)
        return [];
    if ($n === 1)
        return [$list];

    $result = [];
    $i = 0;
    while ($i < $n) {
        if ($i + 2 >= $n) {
            // push remaining elements as singletons
            for (; $i < $n; $i++) {
                $result[] = [$list[$i]];
            }
            break;
        }
        $x  = $list[$i];
        $op = $list[$i + 1];
        $y  = $list[$i + 2];
        if (is_infix_operator($op)) {
            $result[] = [$x, $op, $y];
            $i += 3;
        } else {
            $result[] = [$x];
            ++$i;
        }
    }
    return [$section, $result];
}

function Not($token) {
    if (is_string($token)) {
        if (str_starts_with($token, 'Not'))
            return substr($token, 3);
        elseif (str_starts_with($token, 'Eq'))
            return "Ne" . substr($token, 2);
        elseif (str_starts_with($token, 'Ne'))
            return "Eq" . substr($token, 2);
        else
            return "Not" . $token;
    }
    if (count($token) == 1)
        return [Not($token[0])];
    return $token;
}
