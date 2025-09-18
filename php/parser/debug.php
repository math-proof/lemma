<?php
require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/lean.php';

function main() {
    $file = "Lemma/Trigonometry/Arg/eq/Ite__Ite_Arccos/of/Ne_0.lean";
    $file = "../../$file";
    $code = file_get_contents($file);
    $root = LeanParser::$instance->build($code);
    echo str_replace(" ", '&nbsp;', str_replace("\n", '<br>', "$root"));
}

#[Attribute(Attribute::TARGET_METHOD)]
class Logging implements std\DecoratorAttribute {
    public function __construct(private ?string $message = null) {}

    public function getCallback(callable $wrapped, \ReflectionMethod $method): callable {
        $msg = $this->message ?: "Method {$method->getName()}";
        return function(...$args) use ($wrapped, $msg) {
            echo "{$msg} called with: " . json_encode($args) . "\n";
            $result = $wrapped(...$args);
            echo "{$msg} returned: " . json_encode($result) . "\n";
            return $result;
        };
    }

    public function __init__(string $class, string $method) {}
}

#[Attribute(Attribute::TARGET_METHOD)]
class Memorize implements std\DecoratorAttribute {

    public function getCallback(callable $wrapped, \ReflectionMethod $method): callable {
        $cache = [];
        return function(...$args) use ($wrapped, $method, &$cache) {
            $key = md5($method->getName() . serialize($args));
            if (!isset($cache[$key])) {
                $cache[$key] = $wrapped(...$args);
            }
            else
                echo "return cache data ";
            return $cache[$key];
        };
    }
    public function __init__(string $class, string $method) {}
}


class Calculator { 
    use std\MethodDecorator;

    #[Logging('Adding numbers')]
    #[Memorize]
    protected static function add(int $a, int $b): int {
        echo "Performing add...\n";
        return $a + $b;
    }

    #[Logging('Subtracting numbers')]
    #[Memorize]
    protected function subtract(int $a, int $b): int {
        return $a - $b;
    }
}

function test() {
// static method decorator Demonstration
echo Calculator::add(3, 5) .'<br>'; // Logs and memoizes
echo Calculator::add(3, 5) .'<br>'; // Returns memoized result

// object method decorator Demonstration
$calc = new Calculator();
echo $calc->subtract(10, 7) .'<br>'; // Logs and memoizes
echo $calc->subtract(10, 7) .'<br>'; // Logs and memoizes
}

main();
