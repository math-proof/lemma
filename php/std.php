<?php
// use the following regex to remove error_log prints:
// ^ *error_log
namespace std;

use Iterator, JsonSerializable, IteratorAggregate, RuntimeException, Exception, Traversable;
use curl_init, curl_setopt, curl_exec, curl_errno, curl_close;
use mb_detect_encoding, mb_convert_encoding;
use SplMinHeap;
use usleep;

// implement common collections like: Set, Queue, Graph
class QueueIterator implements Iterator
{

    private $_queue;

    private $_index;

    public function __construct($array)
    {
        $this->_queue = $array;
        $this->_index = 0;
    }

    // Rewind the Iterator to the first element
    public function rewind(): void
    {
        $this->_index = 0;
    }

    // Return the current element
    public function current(): mixed
    {
        return $this->_queue->get($this->_index);
    }

    // Return the key of the current element
    public function key(): mixed
    {
        return $this->_index;
    }

    // Move forward to next element
    public function next(): void
    {
        ++ $this->_index;
        // return $this;
    }

    // Checks if current position is valid
    public function valid(): bool
    {
        return $this->_index < $this->_queue->size();
    }
}

/**
 * Class Queue for FIFO
 */
class Queue implements JsonSerializable, IteratorAggregate
{

    /**
     *
     * @var int pointer to the front
     *
     */
    private $_start;

    /**
     *
     * @var int pointer to the rear
     *
     */
    private $_stop;

    /**
     *
     * @var array data
     *
     */
    private $_array;

    /**
     *
     * @var int the actual capacity of queue;
     *
     */
    private $_capacity;

    /**
     *
     * Queue constructor.
     *
     * @param int $capacity
     *
     */
    public function __construct($capacity = 4)
    {
        $this->_array = [];

        $this->_start = 0;

        $this->_stop = 0;

        $this->_capacity = $capacity;
    }

    /**
     * destructor
     */
    public function __destruct()
    {
        unset($this->_array);
    }

    /**
     *
     * @method enqueue
     *
     * @param mixed $elem
     *
     * @return bool
     *
     */
    public function push($elem)
    {
        if ($this->size() == $this->_capacity) {
            $this->expand();
        }

        $this->_array[$this->_stop % $this->_capacity] = $elem;

        ++ $this->_stop;
    }

    private function expand()
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }

        $this->_capacity *= 2;
        $this->_start = 0;
        $this->_stop = count($array);
        $this->_array = $array;
    }

    /**
     *
     * @method dequeue
     *
     * @return mixed|null
     *
     */
    public function pop()
    {
        if ($this->isEmpty())
            return null;

        $elem = $this->_array[$this->_start];

        ++ $this->_start;

        if ($this->_start == $this->_capacity) {
            $this->_start = 0;
            $this->_stop -= $this->_capacity;
        }

        return $elem;
    }

    /**
     *
     * @method check whether the queue is empty
     *
     * @return bool
     *
     */
    public function isEmpty()
    {
        return $this->size() === 0;
    }

    public function size()
    {
        assert($this->_stop >= $this->_start);
        return $this->_stop - $this->_start;
    }

    public function capacity()
    {
        return $this->_capacity;
    }

    public function get($index)
    {
        assert($index >= 0);
        assert($index < $this->size(), "index out of bound, index = $index, size = " . $this->size());

        $index += $this->_start;
        if ($index >= $this->_capacity) {
            $index -= $this->_capacity;
        }

        return $this->_array[$index];
    }

    // Required definition of interface IteratorAggregate
    public function getIterator(): Traversable
    {
        return new QueueIterator($this);
    }

    /**
     *
     * @method clear the whole queue.
     *
     */
    public function clear()
    {
        $this->_array = [];
        $this->_start = 0;
        $this->_stop = 0;
    }

    public function jsonSerialize(): mixed
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }

        return $array;
    }
}

class SetIterator implements Iterator
{

    private $_array;

    private $_valid;

    private $_index;

    public function __construct($array)
    {
        $this->_array = $array;
    }

    // Rewind the Iterator to the first element
    public function rewind(): void
    {
        reset($this->_array);
        $this->_index = 0;
        $this->_valid = count($this->_array) ? true : false;
    }

    // Return the current element
    public function current(): mixed
    {
        return key($this->_array);
    }

    // Return the key of the current element
    public function key(): mixed
    {
        return $this->_index;
    }

    // Move forward to next element
    public function next(): void
    {
        $this->_valid = next($this->_array) === false ? false : true;
        ++ $this->_index;
        // return $this;
    }

    // Checks if current position is valid
    public function valid(): bool
    {
        return $this->_valid;
    }
}

class Set implements JsonSerializable, IteratorAggregate
{

    private $set;

    public function __construct($array = [])
    {
        $this->set = [];
        $this->addAll($array);
    }

    public function add($element)
    {
        $this->set[$element] = true;
    }

    public function addAll($elements)
    {
        foreach ($elements as $e) {
            $this->set[$e] = true;
        }
    }

    public function peek()
    {
        foreach ($this as $e) {
            return $e;
        }
    }

    public function complement($set)
    {
        $complement = new Set();
        foreach ($this as $e) {
            if (! $set->contains($e))
                $complement->add($e);
        }
        return $complement;
    }

    public function remove($element)
    {
        unset($this->set[$element]);
    }

    public function removeAll($elements)
    {
        foreach ($elements as $e) {
            unset($this->set[$e]);
        }
    }

    public function enumerate()
    {
        foreach ($this->set as $key => &$_) {
            yield $key;
        }
    }

    public function contains($element)
    {
        return array_key_exists($element, $this->set);
    }

    public function isEmpty()
    {
        return count($this->set) == 0;
    }

    // Required definition of interface IteratorAggregate
    public function getIterator(): Traversable
    {
        return new SetIterator($this->set);
    }

    public function jsonSerialize(): mixed
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }
        return $array;
    }

    public function __toString()
    {
        return encode($this->jsonSerialize());
    }
}

class Graph implements JsonSerializable, IteratorAggregate
{

    public $graph;

    private $permanent_mark;

    private $temporary_mark;

    function visit($n)
    {
        // error_log("visiting key = $n");
        if ($this->permanent_mark->contains($n))
            return null;

        if ($this->temporary_mark->contains($n))
            return $n;

        if (array_key_exists($n, $this->graph)) {

            $this->temporary_mark->add($n);
            // error_log("this->graph[n] = " . encode($this->graph[$n]));

            foreach ($this->graph[$n] as $m) {
                $node = $this->visit($m);
                if ($node != null)
                    return $node;
            }

            $this->temporary_mark->remove($n);
        }

        $this->permanent_mark->add($n);
        return null;
    }

    function visit_and_traceback($n, &$parent)
    {
        // error_log("visiting key = $n");
        if ($this->permanent_mark->contains($n))
            return null;

        if ($this->temporary_mark->contains($n)) {
            return $n;
        }

        if (array_key_exists($n, $this->graph)) {

            $this->temporary_mark->add($n);
            // error_log("this->graph[n] = " . encode($this->graph[$n]));

            foreach ($this->graph[$n] as $m) {
                $node = $this->visit_and_traceback($m, $parent);
                if ($node != null) {
                    $parent[] = $m;
                    return $node;
                }
            }

            $this->temporary_mark->remove($n);
        }

        $this->permanent_mark->add($n);
        return null;
    }

    function initialize_topology()
    {
        $this->permanent_mark = new Set();
        $this->temporary_mark = new Set();
    }

    function &topological_sort_depth_first()
    {
        $this->initialize_topology();
        foreach ($this->graph as $n => $_) {
            if ($this->visit($n))
                return null;
        }

        return $this->L;
    }

    function detect_cycle($key)
    {
        $this->initialize_topology();
        return $this->visit($key);
    }

    function detect_cycle_traceback($key, &$parent)
    {
        $this->initialize_topology();
        $this->visit_and_traceback($key, $parent);
    }

    public function __construct()
    {
        $this->graph = [];
    }

    function convert_set_to_list()
    {
        foreach ($this->graph as $key => &$value) {
            $this->graph[$key] = iterator_to_array($value->enumerate());
        }
    }

    function insert($from, $to)
    {
        if (! array_key_exists($from, $this->graph)) {
            $this->graph[$from] = new Set();
        }

        $this->graph[$from]->add($to);
    }

    // Required definition of interface IteratorAggregate
    public function getIterator(): Traversable
    {
        return new GraphIterator($this->graph);
    }

    public function jsonSerialize(): mixed
    {
        return $this->graph;
    }
}

class GraphIterator implements Iterator
{

    private $_array;

    private $_valid;

    private $set_iterator;

    private $_key = 0;

    public function __construct($array)
    {
        $this->_array = $array;
        $this->_valid = count($this->_array) ? true : false;
    }

    // Rewind the Iterator to the first element
    public function rewind(): void
    {
        reset($this->_array);
        $this->set_iterator = current($this->_array)->getIterator();
    }

    // Return the current element
    public function current(): mixed
    {
        return [
            key($this->_array),
            $this->set_iterator->current()
        ];
    }

    // Return the key of the current element
    public function key(): mixed
    {
        return $this->_key;
    }

    // Move forward to next element
    public function next(): void
    {
        $this->set_iterator->next();
        if ($this->set_iterator->valid()) {
            $this->_valid = true;
        } else {
            $this->_valid = next($this->_array) === false ? false : true;
            if ($this->_valid) {
                $this->set_iterator = current($this->_array)->getIterator();
            }
        }
        ++ $this->_key;
        // return $this;
    }

    // Checks if current position is valid
    public function valid(): bool
    {
        return $this->_valid;
    }
}

function createDirectory($dir)
{
    if (! is_dir($dir)) {
        if (! mkdir($dir, 0777, true)) {
            throw new RuntimeException("fail to create directory $dir");
        }
    }
}

// delete a non-empty Directory recursively
function deleteDirectory($directory)
{
    if (! file_exists($directory)) {
        return;
    }

    error_log("deleting non-empty directory: $directory");

    if ($dir_handle = opendir($directory)) {

        while ($filename = readdir($dir_handle)) {

            if ($filename != '.' && $filename != '..') {

                $subFile = $directory . "/" . $filename;

                if (is_dir($subFile)) {
                    error_log("deleting folder: $subFile");
                    deleteDirectory($subFile);
                } elseif (is_file($subFile)) {
                    error_log("deleting file: $subFile");
                    unlink($subFile);
                }
            }
        }

        closedir($dir_handle);

        if (rmdir($directory) !== true) {
            error_log("Warning:  rmdir($directory): Directory not empty! trying popen method");
            if (strtoupper(substr(PHP_OS, 0, 3)) == 'WIN') {
                if (! preg_match("/^\w+:/", $directory)) {
                    $directory = realpath($directory);
                }
                $cmd = "rmdir /s/q $directory";
            } else {
                $cmd = "rm -Rf $directory";
            }

            error_log("executing: " . $cmd);
            pclose(popen($cmd, "r"));
            // $ret = popen($cmd, "r");
            // error_log(fgets($ret));
            // pclose($ret);
        }
    }
}

// delete a non-empty Directory recursively
function renameDirectory($directory, $newDirectory)
{
    createDirectory($newDirectory);
    if (! file_exists($directory)) {
        return;
    }

    if ($dir_handle = opendir($directory)) {

        while ($filename = readdir($dir_handle)) {

            if ($filename != '.' && $filename != '..') {

                $subFile = $directory . "/" . $filename;
                $_subFile = $newDirectory . "/" . $filename;

                if (is_dir($subFile)) {
                    renameDirectory($subFile, $_subFile);
                } elseif (is_file($subFile)) {

                    rename($subFile, $_subFile);
                }
            }
        }

        closedir($dir_handle);

        rmdir($directory);
    }
}

function createNewFile($path)
{
    $dir = dirname($path);
    createDirectory($dir);

    $myfile = fopen($path, "wb");
    if (! $myfile) {
        throw new RuntimeException("fail to create file $path");
    }

    fclose($myfile);
}

class Text implements IteratorAggregate
{

    private $file;

    public function __construct($path, $binary = False)
    {
        // error_log("path = " . $path);
        if (file_exists($path)) {
            $this->file = fopen($path, $binary ? "rb+" : "r+");
        } else {
            createNewFile($path);
            $this->file = fopen($path, $binary ? "wb+" : "w+");
        }

        if ($this->file === false) {
            createNewFile($path);
            $this->file = fopen($path, $binary ? "wb+" : "w+");

            if ($this->file === false) {
                throw new RuntimeException("fail to open file $path");
            }
        }

        $this->rewind();
        // $this->strip = strip
    }

    public function __destruct()
    {
        fclose($this->file);
    }

    // Required definition of interface IteratorAggregate
    public function getIterator(): Traversable
    {
        // error_log("public function getIterator()");
        return new TextIterator($this->file);
    }

    public function rewind()
    {
        // error_log("public function rewind()");
        \rewind($this->file);
        Text::skipByteOrderMark($this->file);
    }

    public function seek($offset, $pivot)
    {
        return fseek($this->file, $offset, $pivot);
    }

    public function end()
    {
        $this->seek(0, SEEK_END);
    }

    public static function skipByteOrderMark($file)
    {
        // error_log("public static function skipByteOrderMark(file)");
        $byteOrderMark = fread($file, 1);

        // error_log("byteOrderMark = " . encode($byteOrderMark));
        if ($byteOrderMark && ord($byteOrderMark) != 0xFEFF) {
            // error_log("rewind() is called again!");
            \rewind($file);
        }
    }

    public function append($s, $end_of_line = "\n")
    {
        $this->end();

        if (is_string($s)) {
            fwrite($this->file, $s . $end_of_line);
        } else {
            foreach ($s as $s) {
                fwrite($this->file, $s . $end_of_line);
            }
        }
    }

    public function flush()
    {
        fflush($this->file);
    }

    public function tell()
    {
        return ftell($this->file);
    }

    public function truncate()
    {
        $pos = $this->tell();

        ftruncate($this->file, $pos);
    }

    public function write($s)
    {
        fwrite($this->file, $s);
    }

    public function writelines($ss)
    {
        $this->rewind();
        fwrite($this->file, implode("\n", $ss));
        $this->truncate();
    }

    public function read($size)
    {
        return fread($this->file, $size);
    }

    public function readlines()
    {
        return iterator_to_array($this);
    }

    public function isEmpty()
    {
        foreach ($this as $line) {
            return False;
        }
        return true;
    }

    public function endsWith($end)
    {
        $this->end();
        $size = strlen($end);
        $offset = $this->tell() - $size;
        if ($offset < 0)
            return False;

        $this->seek($offset, SEEK_SET);

        return $this->read($size) == $end;
    }

    public function setitem($index, $newLine)
    {
        // $this->rewind();
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i == $index)
                $lines[] = $newLine;
            else
                $lines[] = $line;
            ++ $i;
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function insert($index, $newLine)
    {
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i == $index) {
                if (is_array($newLine)) {
                    array_push($lines, ...$newLine);
                } else {
                    $lines[] = $newLine;
                }
            }

            $lines[] = $line;
            ++ $i;
        }

        $this->rewind();
        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function delitem($index)
    {
        error_log("index = $index");
        // $this->rewind();
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i != $index)
                $lines[] = $line;
            ++ $i;
        }

        $this->rewind();

        error_log("lines = " . encode($lines));
        $this->clear();
        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function clear()
    {
        $this->rewind();
        $this->write('');
        $this->truncate();
        $this->flush();
    }

    public function search($regex)
    {
        $regex = "/$regex/";
        // $this->rewind();
        foreach ($this as $line) {
            if (preg_match($regex, $line, $m)) {
                return true;
            }
        }
        return false;
    }

    public function replace($old, $new)
    {
        // $this->rewind();
        $lines = [];
        foreach ($this as $line) {
            $lines[] = str_replace($old, $new, $line);
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function preg_replace($old, $new)
    {
        $old = "/$old/";
        $lines = [];
        foreach ($this as $line) {
            $lines[] = preg_replace($old, $new, $line);
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function preg_match($regex)
    {
        $regex = "/$regex/";
        $lines = [];
        foreach ($this as $line) {
            if (preg_match($regex, $line)) {
                $lines[] = $line;
            }
        }

        return $lines;
    }

    public function retain($regex)
    {
        $regex = "/$regex/";
        $lines = [];
        $linesRemoved = [];
        foreach ($this as $line) {
            if (preg_match($regex, $line)) {
                $lines[] = $line;
            } else {
                $linesRemoved[] = $line;
            }
        }
        $this->writelines($lines);
        return $linesRemoved;
    }
}

class TextIterator implements Iterator
{

    private $file;

    private $line = 0;

    public function __construct($file)
    {
        // error_log("public function TextIterator::__construct(file)");
        $this->file = $file;
    }

    // Rewind the Iterator to the first element
    public function rewind(): void
    {
        // error_log("public function TextIterator::rewind()");
        \rewind($this->file);
        Text::skipByteOrderMark($this->file);
    }

    // Return the current element
    public function current(): mixed
    {
        // error_log("public function current()");
        $line = fgets($this->file);
        // error_log("line = " . $line);
        return rtrim($line);
    }

    // Return the key of the current element
    public function key(): mixed
    {
        // error_log("public function key()");
        return $this->line;
    }

    // Move forward to next element
    public function next(): void
    {
        // error_log("public function next()");
        ++ $this->line;
        // return $this;
    }

    // Checks if current position is valid
    public function valid(): bool
    {
        // error_log("public function valid()");
        // if (is_bool($this->file)) {
        // return false;
        // }
        try {
            return ! feof($this->file);
        } catch (Exception $e) {
            return false;
        }
    }
}

function get_extension($file)
{
    return pathinfo($file, PATHINFO_EXTENSION);
}

function equals($lhs, $rhs)
{
    return ! strcmp($lhs, $rhs);
}

function quote($param)
{
    if (contains($param, "'"))
        $param = str_replace("'", "&apos;", $param);

    return $param;
}

function encode($param, $flag = JSON_UNESCAPED_UNICODE)
{
    return json_encode($param, $flag);
}

function decode($param)
{
    return json_decode($param, true);
}

function list_directory($dir)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (is_dir($temp)) {
                    yield $temp;
                }
            }
            closedir($handle);
        }
    }
}

function iter($str)
{
    foreach (range(strlen($str)) as $i) {
        yield $str[$i];
    }
}

// for example: $ext = 'py', $ext = 'php'
function read_files($dir, $ext = null)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (! is_dir($temp)) {
                    if ($ext == null || equals(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
            closedir($handle);
        }
    }
}

function list_all_files($dir, $ext = null)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if (is_dir($temp)) {
                    // echo 'directory : ' . $temp . '<br>';
                    yield from list_all_files($temp, $ext);
                } else {
                    if (! $ext || equals(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
            closedir($handle);
        }
    }
}

function removedir($dir)
{
    foreach (read_files($dir) as $file) {
        unlink($file);
    }

    foreach (list_directory($dir) as $subdir) {
        removedir($subdir);
    }
    rmdir($dir);
}

function range($start, $stop = null, $step = 1)
{
    if ($stop == null) {
        for ($i = 0; $i < $start; $i += $step) {
            yield $i;
        }
    } else {
        for ($i = $start; $i < $stop; $i += $step) {
            yield $i;
        }
    }
}

function ranged($start, $stop = null, $step = 1)
{
    return [
        ...range($start, $stop, $step)
    ];
}

function establish_hierarchy($node, $select_hierarchy)
{
    $G = [];
    $setProcessed = new Set();

    $queue = new Queue();
    $queue->push($node);

    while (! $queue->isEmpty()) {
        $node = $queue->pop();
        if ($setProcessed->contains($node))
            continue;

        $setProcessed->add($node);

        error_log("setProcessed = " . encode($setProcessed));
        foreach ($select_hierarchy($node) as $child) {
            $queue->push($child);
            $G[$node][] = $child;
        }
    }

    $graph = new Graph();
    foreach ($G as $key => $value) {
        foreach ($value as $node) {
            $graph->insert($key, $node);
        }
    }

    return $graph;
}

// for multi-bytes string slicing
function slice(&$s, $start, $stop = null, $step = 1)
{
    if (is_string($s)) {
        if ($step == 1) {
            if ($stop === null)
                return (new CString($s))->slice($start, $stop);
                // return mb_substr($s, $start, $stop, "utf8");

            if ($stop < 0)
                $stop += len($s);

            return (new CString($s))->slice($start, $stop);
            // return mb_substr($s, $start, $stop - $start, "utf8");
        }
        else {
            if ($stop === null)
                $stop = len($s);
            elseif ($stop < 0)
                $stop += len($s);
                    
            return implode('', array_map(fn($i) => slice($s, $i, $i + 1), ranged($start, $stop, $step)));
        }
    } else {
        if ($step == 1) {
            if ($stop === null)
                return array_slice($s, $start);

            if ($stop < 0)
                $stop += count($s);

            return array_slice($s, $start, $stop - $start);
        }
        else {
            if ($stop === null)
                $stop = count($s);
            elseif ($stop < 0)
                $stop += count($s);

            return array_map(fn($i) => $s[$i], ranged($start, $stop, $step));
        }
    }
}

function substring(&$s, $start, $stop = null)
{
    if ($stop === null)
        return substr($s, $start);

    if ($stop < 0)
        $stop += strlen($s);

    return substr($s, $start, $stop - $start);
}

function println($s)
{
    print($s . "\n");
}

function array_insert(&$array, $index, $value)
{
    $newArray = [
        $value
    ];

    if ($index < count($array)) {
        $newArray[] = $array[$index];
    }

    array_splice($array, $index, 1, $newArray);
}

function array_delete(&$array, $index)
{
    array_splice($array, $index, 1);
}

function is_linux()
{
    return DIRECTORY_SEPARATOR == '/';
}

function form_post($url, $data = null, $decode = True)
{
    if ($data == null)
        $data = [];

    $postdata = http_build_query($data);

    $opts = [
        'http' => [
            'method' => 'POST',
            'header' => 'Content-type: application/x-www-form-urlencoded',
            'content' => $postdata,
            "timeout" => 3600
        ]
    ];

    $context = stream_context_create($opts);
    $result = file_get_contents($url, false, $context);
    return $decode ? decode($result) : $result;
}

function json_post($url, $data = NULL, $decode = NULL, $stream_id = null)
{
    $curl = curl_init();

    curl_setopt($curl, CURLOPT_URL, $url);
    curl_setopt($curl, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($curl, CURLOPT_SSL_VERIFYHOST, false);
    if (! $data) {
        return 'data is null';
    }

    if (is_array($data)) {
        $data = json_encode($data);
    }
    curl_setopt($curl, CURLOPT_POST, 1);
    curl_setopt($curl, CURLOPT_POSTFIELDS, $data);
    curl_setopt($curl, CURLOPT_HEADER, 0);

    if (is_array($decode)) {
        $header = $decode;
        $decode = null;
    }
    else {
        $header = [];
    }
    
    $header[] = 'Content-Type: application/json; charset=utf-8';
    $header[] = 'Content-Length:' . strlen($data);
    $header[] = 'Cache-Control: no-cache';
    $header[] = 'Pragma: no-cache';
    curl_setopt($curl, CURLOPT_HTTPHEADER, $header);
    curl_setopt($curl, CURLOPT_RETURNTRANSFER, 1);
    if ($stream_id !== null) {
        header('Content-Type: text/event-stream');
        header('Cache-Control: no-cache'); //Prevent Caching
        header('Connection: keep-alive');
        header('X-Accel-Buffering: no');

        curl_setopt($curl, CURLOPT_HTTP_VERSION, CURL_HTTP_VERSION_1_1);
        curl_setopt($curl, CURLOPT_FOLLOWLOCATION, true);
        // https://github.com/qiayue/php-openai-gpt-stream-chat-api-webui
        // ob_start();
        $buffer = '';
        curl_setopt($curl, CURLOPT_WRITEFUNCTION, function($curl, $data) use ($stream_id, &$buffer){
            $size = strlen($data);
            // error_log('$data = '. $data);

            if ($buffer) {
                $data = $buffer.$data;
                $buffer = '';
            }

            $i = strrpos($data, "\n\n");
            if ($i === False) {
                $buffer = $data;
                return $size;
            }

            $i += 2;
            $buffer = substring($data, $i);
            if ($buffer)
                $data = substring($data, 0, $i);

            $lines = explode("\n\n", $data);
            array_pop($lines);
            foreach ($lines as $line) {
                echo "id:$stream_id\n$line\n\n";
                // ob_flush();
                flush();
            }
            return $size;
        });
    }

    $res = curl_exec($curl);
    $errorno = curl_errno($curl);
    if ($errorno) {
        return $errorno;
    }
    curl_close($curl);
    // if ($stream_id !== null) {
        // ob_end_clean();
    // }
    return $decode ? decode($res) : $res;
}

function octet_stream_post($url, $filename, $data = NULL, $decode = NULL)
{
    $curl = curl_init();

    curl_setopt($curl, CURLOPT_URL, $url);
    curl_setopt($curl, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($curl, CURLOPT_SSL_VERIFYHOST, false);
    if (! $data) {
        return 'data is null';
    }

    if (is_array($data))
        $data = json_encode($data);

    curl_setopt($curl, CURLOPT_POST, 1);
    curl_setopt($curl, CURLOPT_POSTFIELDS, $data);
    curl_setopt($curl, CURLOPT_HEADER, 0);
    curl_setopt($curl, CURLOPT_HTTPHEADER, array(
        'Content-Type: application/octet-stream',
        'Content-Length:' . strlen($data),
        "filename: $filename"
    ));
    curl_setopt($curl, CURLOPT_RETURNTRANSFER, 1);
    $res = curl_exec($curl);
    $errorno = curl_errno($curl);
    if ($errorno) {
        return $errorno;
    }
    curl_close($curl);

    return $decode ? decode($res) : $res;
}

function http_get_data($url)
{
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_CUSTOMREQUEST, 'GET');
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_URL, $url);
    ob_start();
    curl_exec($ch);
    $return_content = ob_get_contents();
    ob_end_clean();
    $return_code = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    return $return_content;
}

function saveFile($url, $savePath)
{
    $file_content = http_get_data($url);
    $fp = @fopen($savePath, 'a');
    return fwrite($fp, $file_content);
}

function save($url, $savePath)
{
    $image = file_get_contents($url);
    file_put_contents($savePath, $image); // Where to save the image
}

function detect_encoding($str)
{
    return mb_detect_encoding($str, array(
        "ASCII",
        "GB2312",
        "GBK",
        'BIG5',
        'UTF-8'
    ));
}

function str_to_utf8($str, $current_encode)
{
    return mb_convert_encoding($str, 'UTF-8', $current_encode);
}

class TopKHeap
{

    private $heap;

    private $k;

    public function __construct($k)
    {
        $this->k = $k;
        $this->heap = new SplMinHeap();
    }

    public function push($element)
    {
        if ($this->heap->count() < $this->k) {
            $this->heap->insert($element);
        } else if ($this->heap->top() < $element) {
            $this->heap->extract();
            $this->heap->insert($element);
        }
    }

    public function topk()
    {
        while ($this->heap->count()) {
            $element[] = $this->heap->extract();
        }

        return array_reverse($element);
    }
}

function getParameter($key, $value = '')
{
    if (array_key_exists($key, $_GET))
        return $_GET[$key];

    if (array_key_exists($key, $_POST))
        return $_POST[$key];

    return $value;
}

function removeFrom($value, &$array)
{
    $index = array_search($value, $array);
    array_splice($array, $index, 1);
    // unset ($array[$index]);
}

/**
 * Http Client
 * to enable curl in php7.4, modify D:\wamp64\bin\php\php7.4.13\php.ini
 * ;extension=curl => extension=curl
 */
class HttpClient
{

    /**
     * HttpClient
     *
     * @param array $headers
     *            HTTP header
     */
    public function __construct($headers = array())
    {
        $this->headers = $this->buildHeaders($headers);
        $this->connectTimeout = 60000;
        $this->socketTimeout = 60000;
        $this->conf = array();
    }

    /**
     * 连接超时
     *
     * @param int $ms
     *            毫秒
     */
    public function setConnectionTimeoutInMillis($ms)
    {
        $this->connectTimeout = $ms;
    }

    /**
     * 响应超时
     *
     * @param int $ms
     *            毫秒
     */
    public function setSocketTimeoutInMillis($ms)
    {
        $this->socketTimeout = $ms;
    }

    /**
     * 配置
     *
     * @param array $conf
     */
    public function setConf($conf)
    {
        $this->conf = $conf;
    }

    /**
     * 请求预处理
     *
     * @param resource $ch
     */
    public function prepare($ch)
    {
        foreach ($this->conf as $key => $value) {
            curl_setopt($ch, $key, $value);
        }
    }

    /**
     *
     * @param string $url
     * @param array $data
     *            HTTP POST BODY
     * @param array $param
     *            HTTP URL
     * @param array $headers
     *            HTTP header
     * @return array
     */
    public function post($url, $data = array(), $params = array(), $headers = array())
    {
        $url = $this->buildUrl($url, $params);
        $headers = array_merge($this->headers, $this->buildHeaders($headers));

        $ch = curl_init();
        $this->prepare($ch);
        curl_setopt($ch, CURLOPT_URL, $url);
        curl_setopt($ch, CURLOPT_POST, 1);
        curl_setopt($ch, CURLOPT_HEADER, false);
        curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
        curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
        curl_setopt($ch, CURLOPT_HTTPHEADER, $headers);
        curl_setopt($ch, CURLOPT_POSTFIELDS, is_array($data) ? http_build_query($data) : $data);
        curl_setopt($ch, CURLOPT_TIMEOUT_MS, $this->socketTimeout);
        curl_setopt($ch, CURLOPT_CONNECTTIMEOUT_MS, $this->connectTimeout);
        $content = curl_exec($ch);
        $code = curl_getinfo($ch, CURLINFO_HTTP_CODE);

        if ($code === 0) {
            throw new Exception(curl_error($ch));
        }

        curl_close($ch);

        return array(
            'code' => $code,
            'content' => $content
        );
    }

    /**
     *
     * @param string $url
     * @param array $datas
     *            HTTP POST BODY
     * @param array $param
     *            HTTP URL
     * @param array $headers
     *            HTTP header
     * @return array
     */
    public function multi_post($url, $datas = array(), $params = array(), $headers = array())
    {
        $url = $this->buildUrl($url, $params);
        $headers = array_merge($this->headers, $this->buildHeaders($headers));

        $chs = array();
        $result = array();
        $mh = curl_multi_init();
        foreach ($datas as $data) {
            $ch = curl_init();
            $chs[] = $ch;
            $this->prepare($ch);
            curl_setopt($ch, CURLOPT_URL, $url);
            curl_setopt($ch, CURLOPT_POST, 1);
            curl_setopt($ch, CURLOPT_HEADER, false);
            curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
            curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
            curl_setopt($ch, CURLOPT_HTTPHEADER, $headers);
            curl_setopt($ch, CURLOPT_POSTFIELDS, is_array($data) ? http_build_query($data) : $data);
            curl_setopt($ch, CURLOPT_TIMEOUT_MS, $this->socketTimeout);
            curl_setopt($ch, CURLOPT_CONNECTTIMEOUT_MS, $this->connectTimeout);
            curl_multi_add_handle($mh, $ch);
        }

        $running = null;
        do {
            curl_multi_exec($mh, $running);
            usleep(100);
        } while ($running);

        foreach ($chs as $ch) {
            $content = curl_multi_getcontent($ch);
            $code = curl_getinfo($ch, CURLINFO_HTTP_CODE);
            $result[] = array(
                'code' => $code,
                'content' => $content
            );
            curl_multi_remove_handle($mh, $ch);
        }
        curl_multi_close($mh);

        return $result;
    }

    /**
     *
     * @param string $url
     * @param array $param
     *            HTTP URL
     * @param array $headers
     *            HTTP header
     * @return array
     */
    public function get($url, $params = array(), $headers = array())
    {
        $url = $this->buildUrl($url, $params);
        $headers = array_merge($this->headers, $this->buildHeaders($headers));

        $ch = curl_init();
        $this->prepare($ch);
        curl_setopt($ch, CURLOPT_URL, $url);
        curl_setopt($ch, CURLOPT_HEADER, false);
        curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
        curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
        curl_setopt($ch, CURLOPT_HTTPHEADER, $headers);
        curl_setopt($ch, CURLOPT_TIMEOUT_MS, $this->socketTimeout);
        curl_setopt($ch, CURLOPT_CONNECTTIMEOUT_MS, $this->connectTimeout);
        $content = curl_exec($ch);
        $code = curl_getinfo($ch, CURLINFO_HTTP_CODE);

        if ($code === 0) {
            throw new Exception(curl_error($ch));
        }

        curl_close($ch);
        return array(
            'code' => $code,
            'content' => $content
        );
    }

    /**
     * 构造 header
     *
     * @param array $headers
     * @return array
     */
    private function buildHeaders($headers)
    {
        $result = array();
        foreach ($headers as $k => $v) {
            $result[] = sprintf('%s:%s', $k, $v);
        }
        return $result;
    }

    /**
     *
     * @param string $url
     * @param array $params
     *            参数
     * @return string
     */
    private function buildUrl($url, $params)
    {
        if (! empty($params)) {
            $str = http_build_query($params);
            return $url . (contains($url, '?') ? '&' : '?') . $str;
        } else {
            return $url;
        }
    }
}

function zip(&$arr0, &$arr1, &$arr2=null)
{
    if ($arr2 !== null) {
        $size = min(count($arr0), count($arr1), count($arr2));
        for ($i = 0; $i < $size; ++ $i) {
            yield [
                $arr0[$i],
                $arr1[$i],
                $arr2[$i]
            ];
        }
    }
    else {
        $size = min(count($arr0), count($arr1));
        for ($i = 0; $i < $size; ++ $i) {
            yield [
                $arr0[$i],
                $arr1[$i]
            ];
        }
    }
}

function zipped($arr0, $arr1, $arr2=null)
{
    return iterator_to_array(zip($arr0, $arr1, $arr2));
}

function pop(&$arr, $key, $value = null)
{
    if (array_key_exists($key, $arr)) {
        $value = $arr[$key];
        unset($arr[$key]);
        return $value;
    }

    return $value;
}

function get(&$arr, $key, $value = null)
{
    if ($arr == null)
        return $value;

    if (is_array($arr))
        return array_key_exists($key, $arr) ? $arr[$key] : $value;

    return slice($arr, $key, $key + 1);
}

function batches(&$listOfElement, $batch_size)
{
    $batches = [];

    foreach (range(0, count($listOfElement), $batch_size) as $i) {
        $batches[] = array_slice($listOfElement, $i, min($i + $batch_size, count($listOfElement)) - $i);
    }

    return $batches;
}

function uuid()
{
    $chars = md5(uniqid(mt_rand(), true));
    $uuid = substr($chars, 0, 8) . '-' . substr($chars, 8, 4) . '-' . substr($chars, 12, 4) . '-' . substr($chars, 16, 4) . '-' . substr($chars, 20, 12);
    return $uuid;
}

function makezip($source, $target)
{
    $zip = new \ZipArchive();
    if (is_string($source)) {
        error_log("generating zip file: $target from $source");
        if ($zip->open($target, \ZipArchive::CREATE) === true) {
            foreach (list_all_files($source, '', true) as $file) {
                $zip->addFile($file);
            }
            $zip->close();
        }

        deleteDirectory($source);
    } else {
        error_log("add more files to zip file: $target from a file generator");
        if ($zip->open($target) === true) {
            foreach ($source() as $file) {
                error_log("add $file: to $target");
                $zip->addFile($file);
            }
            $zip->close();
        }
    }

    return $target;
}

function send_from_directory($directory, $path, $as_attachment = true)
{
    $file_path = $directory . "/" . $path;
    $filename = basename($path);

    if (! file_exists($file_path)) {
        echo "! file_exists($file_path)";
        exit();
    }

    $file_size = filesize($file_path);
    Header("Content-type: application/octet-stream");
    Header("Accept-Ranges: bytes");
    Header("Accept-Length:" . $file_size);

    // header('Content-Transfer-Encoding: binary');
    // header('Content-Length: '.filesize($file_path));

    Header("Content-Disposition: attachment; filename=$filename");

    $buffer = 1024;
    $file_count = 0;
    $fp = fopen($file_path, "rb");
    while (! feof($fp) && $file_count < $file_size) {
        $file_con = fread($fp, $buffer);
        $file_count += $buffer;
        // output the content of the file to the browser;
        echo $file_con;
    }

    fclose($fp);
}

abstract class SymbolicSet implements JsonSerializable
{

    public function symmetric_difference($that)
    {
        return $this->union($that) . complement($this->intersects($that));
    }

    public function jaccard($that)
    {
        return $this->intersects($that)->card() / $this->union($that)->card();
    }

    abstract function union($that);

    abstract function intersects($that);

    public function __get($vname)
    {
        switch ($vname) {
            case "is_Range":
            case "is_Rectangle":
            case "is_EmptySet":
            case "is_Union":
                return false;
        }
    }

    public function jsonSerialize(): mixed
    {
        return [];
    }
}

class EmptySet extends SymbolicSet
{

    public function equals($that)
    {
        return $that == null || $that->is_EmptySet;
    }

    public function complement($that)
    {
        return $this;
    }

    public function add($offset)
    {
        return $this;
    }

    public function union($that)
    {
        return $that;
    }

    public function symmetric_difference($that)
    {
        return $that;
    }

    public function intersects($that)
    {
        return $this;
    }

    public function jsonSerialize(): mixed
    {
        return [];
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "is_EmptySet":
                return true;
            case "card":
                return 0;
            default:
                return parent::__get($vname);
        }
    }
}

class Union extends SymbolicSet
{

    public $args;

    public function __construct(...$args)
    {
        $this->args = $args;
    }

    public function intersects($that)
    {
        if ($that->is_EmptySet) {
            return $that;
        }

        $args = [];
        foreach ($this->args as $arg) {
            $arg = $arg->intersects($that);
            if ($arg->is_EmptySet)
                continue;

            if ($arg->is_Union) {
                array_push($args, ...$arg->args);
            } else {
                array_push($args, $arg);
            }
        }

        switch (count($args)) {
            case 0:
                return new EmptySet();
            case 1:
                return $args[0];
            default:
                return new Union(...$args);
        }
    }

    public function equals($that)
    {
        if ($that && $that->is_Union && count($this->args) == count($that->args)) {
            foreach (range(count($this->args)) as $i) {
                if (! $this->args[$i]->equals($that->args[$i]))
                    return false;
            }
            return true;
        }
    }

    public function complement($that)
    {
        $args = [];
        foreach ($this->args as $arg) {
            $arg = $arg->complement($that);
            if ($arg->is_EmptySet)
                continue;

            if ($arg->is_Union) {
                array_push($args, ...$arg->args);
            } else {
                array_push($args, $arg);
            }
        }

        switch (count($args)) {
            case 0:
                return new EmptySet();
            case 1:
                return $args[0];
            default:
                return new Union(...$args);
        }
    }

    public function add($offset)
    {
        return new Union(...array_map(fn ($el) => $el->add($offset), $this->args));
    }

    public function union($that)
    {
        if ($that->is_EmptySet) {
            return $this;
        }

        if ($that->is_Range()) {
            foreach (range(count($this->args)) as $i) {
                $arg = $this->args[i];
                $arg = $arg->union($that);
                if ($arg->is_Range()) {
                    $args = [
                        ...$this->args
                    ];

                    array_delete($args, $i);

                    if (count($args) == 1) {
                        return $args[0]->union($arg);
                    }

                    return (new Union(...$args))->union($arg);
                }
            }

            $args = [
                ...$this->args
            ];
            $index = binary_search($args, $that, function ($a, $b) {
                if ($a->stop <= $b->start)
                    return - 1;

                if ($b->stop <= $a->start)
                    return 1;

                return 0;
            });

            array_insert($args, $index, $that);

            return new Union(...$args);
        } else if ($that->is_Rectangle) {
            foreach (range(count($this->args)) as $i) {
                $arg = $this->args[$i];
                $arg = $arg->union($that);
                if ($arg->is_Rectangle) {
                    $args = [
                        ...$this->args
                    ];

                    array_delete($args, $i);
                    if (count($args) == 1) {
                        return $args[0]->union($arg);
                    }

                    return (new Union(...$args))->union($arg);
                }
            }

            $args = [
                ...$this->args
            ];

            $index = binary_search($args, $that, function ($lhs, $rhs) {
                if ($lhs->x < $rhs->x)
                    return - 1;

                if ($lhs->x > $rhs->x)
                    return 1;

                if ($lhs->y < $rhs->y)
                    return - 1;

                if ($lhs->y > $rhs->y)
                    return 1;

                if ($lhs->width < $rhs->width)
                    return - 1;

                if ($lhs->width > $rhs->width)
                    return 1;

                if ($lhs->height < $rhs->height)
                    return - 1;

                if ($lhs->height > $rhs->height)
                    return 1;

                return 0;
            });

            array_insert($args, $index, $that);

            return (new Union(...$args))->try_union();
        }

        foreach ($this->args as $arg) {
            $that = $that->union($arg);
        }

        return $that;
    }

    public function union_without_merging($that)
    {
        if ($that->is_EmptySet)
            return $this;

        if ($that->is_Range) {
            foreach ($this->args as &$arg)
                $that = $that->complement($arg);

            if ($that->is_EmptySet)
                return $this;

            if ($that->is_Range)
                $that = [
                    $that
                ];
            else
                $that = $that->args;

            $args = [
                ...$this->args
            ];

            foreach ($that as &$that)
                array_insert($args, binary_search($args, $that, fn ($lhs, $rhs) => $lhs->compareTo($rhs)), $that);

            return new Union(...$args);
        }

        if ($that->is_Union) {
            $self = $this;
            foreach ($that->args as &$arg) {
                $self = $self->union_without_merging($arg);
            }
            return $self;
        }
    }

    public function sliced($obj)
    {
        return implode('\t', array_map(fn ($domain) => $domain->sliced($obj), $this->args));
    }

    public function jsonSerialize(): mixed
    {
        $array = [];
        foreach ($this->args as $value) {
            $array[] = $value->jsonSerialize();
        }

        return [
            "args" => $array
        ];
    }

    public function try_union()
    {
        // http://localhost/axiom/?module=Set.Eq_Card.Subset.to.Eq
        $bbox = $this->bbox();
        return $this->card() == $bbox->card() ? $bbox : $this;
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "is_Union":
                return true;

            case "card":
                $card = 0;
                foreach ($this->args as $arg) {
                    $card += $arg->card();
                }

                return $card;

            case "bbox":
                $x_min = INF;
                $y_min = INF;
                $x_max = - INF;
                $y_max = - INF;
                foreach ($this->args as $rect) {
                    $x_min = min($x_min, $rect->x);
                    $y_min = min($y_min, $rect->y);
                    $x_max = max($x_max, $rect->x_stop());
                    $y_max = max($y_max, $rect->y_stop());
                }

                return new Rectangle($x_min, $y_min, $x_max - $x_min, $y_max - $y_min);

            default:
                return parent::__get($vname);
        }
    }

    public function __toString()
    {
        return implode(" | ", array_map(fn ($arg) => "$arg", $this->args));
    }
}

class Range extends SymbolicSet
{

    public function __get($vname)
    {
        switch ($vname) {
            case "is_Range":
                return true;

            case "card":
                return $this->stop - $this->start;

            default:
                return parent::__get($vname);
        }
    }

    public $start, $stop;

    public function __construct($start, $stop)
    {
        $this->start = $start;
        $this->stop = $stop;
    }

    public function intersects($that)
    {
        if ($that->is_Union) {
            return $that->intersects($this);
        }

        $start = $that->start;
        $stop = $that->stop;

        if ($start >= $this->stop || $stop <= $this->start)
            return new EmptySet();

        return new Range(max($this->start, $start), min($this->stop, $stop));
    }

    public function equals($that)
    {
        if ($that && $that->is_Range()) {
            return $this->start == $that->start && $this->stop == $that->stop;
        }
    }

    public function union($that)
    {
        if ($that->is_Range()) {
            $start = $that->start;
            $stop = $that->stop;

            if ($start > $this->stop)
                return new Union($this, $that);

            if ($stop < $this->start)
                return new Union($that, $this);

            return new Range(min($this->start, $start), max($this->stop, $stop));
        }

        if ($that->is_EmptySet)
            return $this;

        return $that->union($this);
    }

    public function union_without_merging($that)
    {
        if ($that->is_EmptySet)
            return $this;

        if ($that->is_Range) {
            $start = $that->start;
            $stop = $that->stop;
            if ($start >= $this->stop)
                return new Union($this, $that);

            if ($stop <= $this->start)
                return new Union($that, $this);

            $mid = $this->intersects($that);
            $lhs = $this->complement($that);
            $rhs = $that->complement($this);
            if ($rhs->is_EmptySet)
                return $mid->union_without_merging($lhs);

            if ($lhs->is_EmptySet)
                return $mid->union_without_merging($rhs);

            if ($lhs->start > $rhs->start)
                [
                    $lhs,
                    $rhs
                ] = [
                    $rhs,
                    $lhs
                ];

            return new Union($lhs, $mid, $rhs);
        }

        return $that->union_without_merging($this);
    }

    public function complement($that)
    {
        if ($that->start >= $this->stop)
            return $this;

        if ($that->start > $this->start) {
            // now that that.start < this.stop
            if ($that->stop >= $this->stop)
                return new Range($this->start, $that->start);

            // now that that.stop < this.stop
            return new Union(new Range($this->start, $that->start), new Range($that->stop, $this->stop));
        } else {
            // now that that.start <= this.start
            if ($that->stop >= $this->stop)
                return new EmptySet();

            // now that that.stop < this.stop
            if ($that->stop > $this->start)
                return new Range($that->stop, $this->stop);

            return new Range($this->start, $this->stop);
        }
    }

    public function add($offset)
    {
        return new Range($this->start + $offset, $this->stop + $offset);
    }

    public function sliced($obj)
    {
        return slice($obj, $this->start, $this->stop);
    }

    public function jsonSerialize(): mixed
    {
        return [
            "start" => $this->start,
            "stop" => $this->stop
        ];
    }

    public function compareTo($that)
    {
        if ($this->stop <= $that->start)
            return - 1;

        if ($that->stop <= $this->start)
            return 1;

        return 0;
    }

    public function __toString()
    {
        return "[$this->start; $this->stop)";
    }

    public function contains($pt) {
        if (is_float($pt)) {
            return $pt >= $this->start && $pt < $this->stop;
        }
        else {
            return $pt->start >= $this->start && $pt->stop <= $this->stop;
        }
    }
}

class Rectangle extends SymbolicSet
{

    public $x, $y, $width, $height;

    public function __construct($x, $y, $width, $height)
    {
        $this->x = $x;
        $this->y = $y;
        $this->width = $width;
        $this->height = $height;
    }

    public function jsonSerialize(): mixed
    {
        return [
            "x" => $this->x,
            "y" => $this->y,
            "width" => $this->width,
            "height" => $this->height
        ];
    }

    public function x_stop($x_stop = null)
    {
        if ($x_stop === null)
            return $this->x + $this->width;

        $this->width = $x_stop - $this->x;
    }

    public function y_stop($y_stop = null)
    {
        if ($y_stop === null)
            return $this->y + $this->height;

        $this->height = $y_stop - $this->y;
    }

    public function intersects($that)
    {
        if ($that->is_Union)
            return $that->intersects($this);

        $x = $that->x;
        $y = $that->y;
        $x_stop = $that->x_stop();
        $y_stop = $that->y_stop();

        if ($x >= $this->x_stop() || $x_stop <= $this->x || $y >= $this->y_stop() || $y_stop <= $this->y)
            return new EmptySet();

        $x = max($this->x, $x);
        $x_stop = min($this->x_stop(), $x_stop);

        $y = max($this->y, $y);
        $y_stop = min($this->y_stop(), $y_stop);

        $width = $x_stop - $x;
        $height = $y_stop - $y;
        return new Rectangle($x, $y, $width, $height);
    }

    public function equals($that)
    {
        if ($that && $that->is_Rectangle) {
            return $this->x == $that->x && $this->width == $that->width && $this->y == $that->y && $this->height == $that->height;
        }
    }

    public function union($that)
    {
        if ($that->is_Rectangle) {
            $x = $that->x;
            $y = $that->y;
            $x_stop = $that->x_stop();
            $y_stop = $that->y_stop();

            if ($x == $this->x && $x_stop == $this->x_stop()) {
                if ($y == $this->y_stop())
                    return new Rectangle($this->x, $this->y, $this->width, $this->height + $that->height);
                if ($this->y == $y_stop)
                    return new Rectangle($x, $y, $this->width, $this->height + $that->height);
            } else if ($y == $this->y && $y_stop == $this->y_stop()) {
                if ($x == $this->x_stop())
                    return new Rectangle($this->x, $this->y, $this->width + $that->width, $this->height);
                if ($this->x == $x_stop)
                    return new Rectangle($x, $y, $this->width + $that->width, $this->height);
            }

            return new Union($this, $that);
        }

        if ($that->is_EmptySet)
            return $this;

        return $that->union($this);
    }

    public function complement($that)
    {
        if ($that->is_Rectangle) {
            if ($that->x >= $this->x_stop() || $that->y >= $this->y_stop() || $that->x_stop() <= $this->x || $that->y_stop() <= $this->y)
                return $this;

            // that.x < this.x_stop && that.x_stop > this.x
            // that.y < this.y_stop && that.y_stop > this.y
            if ($that->x <= $this->x) {
                if ($that->x_stop() < $this->x_stop()) {
                    // that.x <= this.x && that.x_stop < this.x_stop
                    if ($that->y <= $this->y) {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y <= this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $that->y_stop(), $this->width, $this->y_stop() - $that->y_stop()), new Rectangle($that->x_stop(), $this->y, $this->x_stop() - $that->x_stop(), $that->y_stop() - $this->y));
                        else
                            // that.y <= this.y && that.y_stop >= this.y_stop
                            return new Rectangle($that->x_stop(), $this->y, $this->x_stop() - $that->x_stop(), $this->height);
                    } else {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y > this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y_stop(), $this->width, $this->y_stop() - $that->y_stop()), new Rectangle($that->x_stop(), $that->y, $this->x_stop() - $that->x_stop(), $that->height));
                        else
                            // that.y > this.y && that.y_stop >= this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($that->x_stop(), $that->y, $this->x_stop() - $that->x_stop(), $this->y_stop() - $that->y));
                    }
                } else {
                    // that.x <= this.x && that.x_stop >= this.x_stop
                    if ($that->y <= $this->y) {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y <= this.y && that.y_stop < this.y_stop
                            return new Rectangle($this->x, $that->y_stop(), $this->width, $this->y_stop() - $that->y_stop());
                        else
                            // that.y <= this.y && that.y_stop >= this.y_stop
                            return new EmptySet();
                    } else {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y > this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y_stop(), $this->width, $this->y_stop() - $that->y_stop()));
                        else
                            // that.y > this.y && that.y_stop >= this.y_stop
                            return new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y);
                    }
                }
            } else {
                if ($that->x_stop() < $this->x_stop()) {
                    // that.x > this.x && that.x_stop < this.x_stop
                    if ($that->y <= $this->y) {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y <= this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $that->x - $this->x, $this->height), new Rectangle($that->x, $that->y_stop(), $this->x_stop() - $that->x, $this->y_stop() - $that->y_stop()), new Rectangle($that->x_stop(), $this->y, $this->x_stop() - $that->x_stop(), $that->y_stop() - $this->y));
                        else
                            // that.y <= this.y && that.y_stop >= this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $that->x - $this->x, $this->height), new Rectangle($that->x_stop(), $this->y, $this->x_stop() - $that->x_stop(), $that->height));
                    } else {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y > this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y, $that->x - $this->x, $this->y_stop() - $that->y), new Rectangle($that->x, $that->y_stop(), $this->x_stop() - $this->x, $this->y_stop() - $that->y_stop()), new Rectangle($that->x_stop(), $that->y, $this->x_stop() - $that->x_stop(), $that->height));
                        else
                            // that.y > this.y && that.y_stop >= this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y, $that->x - $this->x, $this->y_stop() - $that->y), new Rectangle($that->x_stop(), $that->y, $this->x_stop() - $that->x_stop(), $this->y_stop() - $that->y));
                    }
                } else {
                    // that.x > this.x && that.x_stop >= this.x_stop
                    if ($that->y <= $this->y) {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y <= this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $that->x - $this->x, $this->height), new Rectangle($that->x, $that->y_stop(), $this->x_stop() - $that->x, $this->y_stop() - $that->y_stop()));
                        else
                            // that.y <= this.y && that.y_stop >= this.y_stop
                            return new Rectangle($this->x, $this->y, $that->x - $this->x, $this->height);
                    } else {
                        if ($that->y_stop() < $this->y_stop())
                            // that.y > this.y && that.y_stop < this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y, $that->x - $this->x, $this->y_stop() - $that->y), new Rectangle($that->x, $that->y_stop(), $this->x_stop() - $this->x, $this->y_stop() - $that->y_stop()));
                        else
                            // that.y > this.y && that.y_stop >= this.y_stop
                            return new Union(new Rectangle($this->x, $this->y, $this->width, $that->y - $this->y), new Rectangle($this->x, $that->y, $that->x - $this->x, $this->y_stop() - $that->y));
                    }
                }
            }
        } else if ($that->is_EmptySet) {
            return $this;
        } else if ($that->is_Union) {
            $self = $this;
            foreach ($that->args as $region) {
                $self = $self->complement($region);
            }

            return $self;
        }
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "is_Rectangle":
                return true;
            case "card":
                return $this->width * $this->height;
            case "args":
                return [
                    $this->x,
                    $this->y,
                    $this->width,
                    $this->height
                ];
            default:
                return parent::__get($vname);
        }
    }

    public function add($offset_x, $offset_y)
    {
        return new Rectangle($this->x + $offset_x, $this->y + $offset_y, $this->width, $this->height);
    }

    public function distance($x0, $y0)
    {
        if ($x0 < $this->x) {
            if ($y0 < $this->y)
                return sqrt(pow($x0 - $this->x, 2) + pow($y0 - $this->y, 2));

            if ($y0 < $this->y_stop())
                return abs($x0 - $this->x);

            return sqrt(pow($x0 - $this->x, 2) + pow($y0 - $this->y_stop(), 2));
        }

        if ($x0 < $this->x_stop()) {
            if ($y0 < $this->y)
                return abs($y0 - $this->y);

            if ($y0 < $this->y_stop())
                return 0;

            return abs($y0 - $this->y_stop());
        }

        if ($y0 < $this->y)
            return sqrt(pow($x0 - $this->x_stop(), 2) + pow($y0 - $this->y, 2));

        if ($y0 < $this->y_stop())
            return abs($x0 - $this->x_stop());

        return sqrt(pow($x0 - $this->x_stop(), 2) + pow($y0 - $this->y_stop(), 2));
    }
}

function binary_search(&$arr, &$value, $compareTo)
{
    $begin = 0;
    $end = count($arr);
    for (;;) {
        if ($begin == $end)
            return $begin;

        $mid = $begin + $end >> 1;

        $ret = $compareTo($arr[$mid], $value);
        if ($ret < 0)
            $begin = $mid + 1;
        else if ($ret > 0)
            $end = $mid;
        else
            return $mid;
    }
}

function equal_range(&$self, &$value, $compareTo)
{
    if (! $compareTo)
        $compareTo = fn ($a, $b) => $a - $b;

    $begin = 0;
    $end = count($self);
    for (;;) {
        if ($begin == $end)
            break;

        $mid = $begin + $end >> 1;

        $ret = $compareTo($self[$mid], $value);
        if ($ret < 0)
            $begin = $mid + 1;
        else if ($ret > 0)
            $end = $mid;
        else {
            $stop = $begin - 1;
            $begin = $mid;
            for (;;) {
                $pivot = - (- $begin - $stop >> 1);
                if ($pivot == $begin)
                    break;

                if ($compareTo($self[$pivot], $value))
                    $stop = $pivot;
                else
                    $begin = $pivot;
            }

            for (;;) {
                $pivot = $mid + $end >> 1;
                if ($pivot == $mid)
                    break;

                if ($compareTo($self[$pivot], $value))
                    $end = $pivot;
                else
                    $mid = $pivot;
            }

            break;
        }
    }
    return [
        $begin,
        $end
    ];
}

function enumerate(&$array)
{
    foreach (range(count($array)) as $i) {
        yield [
            $i,
            $array[$i]
        ];
    }
}

function array_repeat($array, $count)
{
    $newArray = [];
    foreach (range($count) as $_) {
        foreach ($array as &$el) {
            if (is_array($el)) {
                $el = [
                    ...$el
                ];
            }
            array_push($newArray, $el);
        }
    }
    return $newArray;
}

function array_all($fn, $array)
{
    foreach ($array as &$element) {
        if (! $fn($element))
            return false;
    }
    return true;
}

function array_any($fn, $array)
{
    foreach ($array as &$element) {
        if ($fn($element))
            return true;
    }

    return false;
}

function hump($str)
{
    return preg_replace_callback("/_[a-z]/", fn ($s) => strtoupper(substring($s[0], 1)), $str);
}

function contains($str, $char)
{
    return strpos($str, $char) !== false;
}

function range_cmp(&$lhs, &$rhs)
{
    if ($lhs['end'] <= $rhs['start'])
        return - 1;

    if ($lhs['start'] >= $rhs['end'])
        return 1;

    return 0;
}

class CString implements IteratorAggregate
{

    public $string;

    private $physicalOffset;

    public function __construct($string)
    {
        $this->string = $string;

        $physicalOffset = [];
        foreach ($this as $key => $value) {
            $physicalOffset[] = [
                $key,
                $key + strlen($value)
            ];
        }

        $this->physicalOffset = $physicalOffset;
    }

    // Required definition of interface IteratorAggregate
    public function getIterator(): Traversable
    {
        return new CStringIterator($this->string);
    }

    public function get($index)
    {
        return substring($this->string, ...$this->physicalOffset[$index]);
    }

    public function get_utf8($start, $end)
    {
        return substring($this->string, $start, $end);
    }

    public function slice($start, $end)
    {
        return $this->get_utf8($this->physicalOffset[$start][0], $this->physicalOffset[$end - 1][1]);
    }

    public function back()
    {
        return substring($this->string, ...end($this->physicalOffset));
    }

    public function isEmpty()
    {
        return ! $this->string;
    }

    public function endsWith($end)
    {
        return endsWith($this->string, $end);
    }

    public function physical2logical($physicalOffset)
    {
        return binary_search($this->physicalOffset, $physicalOffset, function ($lhs, $rhs) {
            [
                $start,
                $end
            ] = $lhs;
            if ($end <= $rhs)
                return - 1;

            if ($start > $rhs)
                return 1;

            return 0;
        });
    }

    public function __get($vname)
    {
        switch ($vname) {
            case "length":
                return count($this->physicalOffset);
        }
        return null;
    }

    public static function utf8ByteSize($byte)
    {
        // for error: return 0
        // for valid results: return 1-6
        // never return other value

        // UTF8 encoding format：
        // closed integer interval   0        1        2        3        4        5
        // [U-00000000, U-0000007F]: 0xxxxxxx
        // [U-00000080, U-000007FF]: 110xxxxx 10xxxxxx
        // [U-00000800, U-0000FFFF]: 1110xxxx 10xxxxxx 10xxxxxx
        // [U-00010000, U-001FFFFF]: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        // [U-00200000, U-03FFFFFF]: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
        // [U-04000000, U-7FFFFFFF]: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
        $byte = ord($byte);

        $len = 0;
        $mask = 0x80;
        while ($byte & $mask) {
            ++ $len;
            if ($len > 6) {
                println(__FUNCTION__);
                println("illegal char encountered" . $byte);
                // cerr << "The mask get len is over 6." << endl;
                return 0;
            }
            $mask >>= 1;
        }

        if (0 == $len)
            return 1;

        return $len;
    }

    // precondition: $wc is an unicode integer,
    public static function unicode2utf($wc)
    {
        // https://blog.csdn.net/qq_38279908/article/details/89329740
        // https://www.cnblogs.com/cfas/p/7931787.html
        // return std::wstring_convert<std::codecvt_utf8<wchar_t> >().to_bytes(wstr);
        if (is_string($wc)) {
            return $wc;
        }
        
        $pText = [];
        
        if (is_array($wc)) {
            foreach (range(count($wc)) as $i) {
                $pText[] = self::unicode2utf($wc[$i]);
            }

            return implode('', $pText);
        }

        if (! ($wc & ~ 0x0000007F)) {
            // U-00000000 - U-0000007F: 0xxxxxxx
            $pText[] = $wc;
            // $pText[] = 0;
        } else if (! ($wc & ~ 0x000007FF)) {
            // U-00000080 - U-000007FF: 110xxxxx 10xxxxxx
            $pText[] = 0xC0 | (($wc >> 6) & 0x1F);
            $pText[] = 0x80 | ($wc & 0x3F);
            // $pText[] = 0;
        } else if (! ($wc & ~ 0x0000FFFF)) {
            // U-00000800 - U-0000FFFF: 1110xxxx 10xxxxxx 10xxxxxx
            $pText[] = 0xE0 | (($wc >> 12) & 0x0F);
            $pText[] = 0x80 | (($wc >> 6) & 0x3F);
            $pText[] = 0x80 | ($wc & 0x3F);
            // $pText[3] = 0;
        } else if (! ($wc & ~ 0x001FFFFF)) {
            // U-00010000 - U-001FFFFF: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
            $pText[] = 0xF0 | (($wc >> 18) & 0x07);
            $pText[] = 0x80 | (($wc >> 12) & 0x3F);
            $pText[] = 0x80 | (($wc >> 6) & 0x3F);
            $pText[] = 0x80 | ($wc & 0x3F);
            // $pText[4] = 0;
        } else if (! ($wc & ~ 0x03FFFFFF)) {
            // U-00200000 - U-03FFFFFF: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
            $pText[] = 0xF8 | (($wc >> 24) & 0x03);
            $pText[] = 0x80 | (($wc >> 18) & 0x3F);
            $pText[] = 0x80 | (($wc >> 12) & 0x3F);
            $pText[] = 0x80 | (($wc >> 6) & 0x3F);
            $pText[] = 0x80 | ($wc & 0x3F);
            // $pText[5] = 0;
        } else {
            // U-04000000 - U-7FFFFFFF: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
            $pText[] = 0xFC | (($wc >> 30) & 0x01);
            $pText[] = 0x80 | (($wc >> 24) & 0x3F);
            $pText[] = 0x80 | (($wc >> 18) & 0x3F);
            $pText[] = 0x80 | (($wc >> 12) & 0x3F);
            $pText[] = 0x80 | (($wc >> 6) & 0x3F);
            $pText[] = 0x80 | ($wc & 0x3F);
            // $pText[6] = 0;
        }

        return implode("", array_map(fn ($ch) => chr($ch), $pText));
    }
}

class CStringIterator implements Iterator
{

    private $string;

    private $strlen;

    private $offset = 0;

    public function __construct($string)
    {
        $this->string = $string;
        $this->strlen = strlen($string);
    }

    // Rewind the Iterator to the first element
    public function rewind(): void
    {
        $this->offset = 0;
    }

    // Return the current element
    public function current(): string
    {
        $offset = $this->offset;
        // error_log("this->string = ".$this->string);
        // error_log("this->string[$offset] = ".$this->string[$offset]);
        // error_log("ord(this->string[$offset]) = ".ord($this->string[$offset]));
        return substr($this->string, $offset, CString::utf8ByteSize($this->string[$offset]));
    }

    // Return the key of the current element
    public function key(): mixed
    {
        return $this->offset;
    }

    // Move forward to next element
    public function next(): void
    {
        $this->offset += CString::utf8ByteSize($this->string[$this->offset]);
        // return $this;
    }

    // Checks if current position is valid
    public function valid(): bool
    {
        return $this->offset < $this->strlen;
    }
}

function &getitem(&$data, $index, ...$indices)
{
    if (count($indices) == 0) {
        if ($data == null)
            return null;

        if (array_key_exists($index, $data))
            return $data[$index];
        else
            return null;
    }

    return getitem($data[$index], ...$indices);
}

function delitem(&$data, $index, ...$indices)
{
    if (count($indices) == 0) {
        if ($data != null) {
            if (array_key_exists($index, $data)) {
                if (is_int($index) && is_list($data))
                    array_delete($data, $index);
                else
                    unset($data[$index]);
            }
        }
    }
    else
        delitem($data[$index], ...$indices);
}

function setitem(&$data, $index, ...$indices)
{
    if (count($indices) == 1) {
        $data[$index] = end($indices);
    } else {
        setitem($data[$index], ...$indices);
    }
}

function sample(&$data, $count)
{
    if ($data && $count) {
        $sample = array_rand($data, $count);
        if ($count > 1)
            return array_map(fn ($i) => $data[$i], $sample);

        return [
            $data[$sample]
        ];
    }
    return $data;
}

function fullmatch($regexp, $str)
{
    $slash = $regexp[0];
    $i = strrpos($regexp, $slash);

    $flags = substr($regexp, $i + 1);
    $regexp = substr($regexp, 1, $i - 1);

    $regexp = "$slash^(?:$regexp)\$$slash$flags";

    if (preg_match($regexp, $str, $m))
        return $m;
    return null;
}

function is_unicode_match(&$regex) {
    foreach (range(strrpos($regex, $regex[0]) + 1, strlen($regex)) as $i) {
        if ($regex[$i] == 'u') {
            return true;
        }
    }
}

function &matchAll($regex, $str, $captureIndex=0)
{
    $matches = [];
    preg_match_all($regex, $str, $matches, PREG_SET_ORDER | PREG_OFFSET_CAPTURE | PREG_UNMATCHED_AS_NULL);
    postprocess_match($matches, $str, $captureIndex, is_unicode_match($regex));
    return $matches;
}

function &matchAllExtended($regex, $str, $captureIndex=0)
{
    $start = 0;
    $matches = [];
    $strlen = strlen($str);
    do {
        if (preg_match($regex, $start? substring($str, $start): $str, $m, PREG_OFFSET_CAPTURE)) {
            [$mText, $index] = $m[0];
            
            if ($start) {
                foreach ($m as &$tuple) {
                    $tuple[1] += $start;
                }
            }
            
            $matches[] = $m;
            $start += $index + strlen($mText);
        }
        else
            break;
    }
    while ($i < $strlen);
    
    postprocess_match($matches, $str, $captureIndex, is_unicode_match($regex));
    return $matches;
}

function postprocess_match(&$matches, &$str, &$captureIndex, $utf8) {
    foreach ($matches as &$m) {
        if (is_array($captureIndex)) {
            $index = [];
            foreach ($captureIndex as $indexCaptured) {
                $index[] = $utf8 ? len(substring($str, 0, $m[$indexCaptured][1])) : $m[$indexCaptured][1];
            }
        }
        else {
            $index = $utf8 ? len(substring($str, 0, $m[$captureIndex][1])) : $m[$captureIndex][1];
        }
        
        foreach (range(count($m)) as $i) {
            if ($m[$i][1] < 0) {
                $m[$i] = null;
            } else {
                $m[$i] = $m[$i][0];
            }
        }
        
        $m = [
            $m,
            $index
        ];
    }
}

function replaceAll($regex, $fn, $str, $join = true)
{
    $newText = [];
    $start = 0;
    $utf8 = is_unicode_match($regex);
    
    foreach (matchAll($regex, $str) as &$matches) {
        [&$m, $index] = $matches;
        if ($start < $index) {
            if ($join)
                $newText[] = $utf8? slice($str, $start, $index) : substring($str, $start, $index);
            else
                $newText[] = [
                    "text" => $utf8? slice($str, $start, $index): substring($str, $start, $index),
                    "start" => $start,
                    "end" => $index
                ];
        }
        
        $start = $index + ($utf8? len($m[0]): strlen($m[0]));
        $newText[] = $fn($matches);
    }

    $end = $utf8? len($str): strlen($str);
    if ($start < $end) {
        $rest = $utf8? slice($str, $start): substring($str, $start);
        if ($join)
            $newText[] = $rest;
        else
            $newText[] = [
                "text" => $rest,
                "start" => $start,
                "end" => $end
            ];
    }

    return $join ? implode('', $newText) : $newText;
}

function indexOf($array, $element)
{
    foreach (enumerate($array) as [
        $index,
        $match
    ]) {
        if ($match == $element)
            return $index;
    }

    return -1;
}

function index($array, $element)
{
    foreach ($array as $key => &$value) {
        if ($value === $element)
            return $key;
    }

    return -1;
}

function deleteIndices(&$arr, $fn, $postprocess = null)
{
    $indicesToDelete = [];
    foreach (range(count($arr)) as $i) {
        if ($fn($arr, $i))
            $indicesToDelete[] = $i;
    }

    if ($indicesToDelete)
        $indicesToDelete = array_reverse($indicesToDelete);

    foreach ($indicesToDelete as $i) {
        if ($postprocess)
            $postprocess($arr, $i);
        array_delete($arr, $i);
    }

    return True;
}

function delete_duplicate(&$list)
{
    $set = new Set();
    deleteIndices($list, function (&$list, $i) use ($set) {
        $item = &$list[$i];
        if ($set->contains($item)) {
            return true;
        }
        $set->add($item);
        return false;
    });
}

function len($s)
{
    if (is_array($s))
        return count($s);

    return (new CString($s))->length;
    // return mb_strlen($s, 'utf8');
}

function add(&$array, $val)
{
    return array_map(fn ($x) => $x + $val, $array);
}

function isspace($s)
{
    return fullmatch("/\s+/u", $s);
}

function entries(&$list)
{
    $result = [];
    foreach ($list as $key => &$value) {
        $result[] = [$key, $value];
    }
    
    return $result;
}

function halve(&$s, $index) {
    return [substring($s, 0, $index), substring($s, $index)];
}

function is_list(&$arr) {
    return is_array($arr) && array_key_exists(0, $arr);
}

function not(&$str) {
    return $str === 0 || $str === '' || $str === null;
}

function json_extract(&$obj, $path) {
    $paths = [];
    foreach (matchAll(substring($path, 1), '/\[(\d+)\]|\.([^.\[\]]+)/') as $m) {
        $paths[] = ($m[2] || (int)$m[1]);
    }
    
    return getitem($obj, ...$paths);
}

function json_remove(&$obj, $path) {
    $paths = [];
    foreach (matchAll('/\[(\d+)\]|\.([^.\[\]]+)/', substring($path, 1)) as [$m, $index]) {
        $paths[] = $m[2]? $m[2]: (int)$m[1];
    }
    
    delitem($obj, ...$paths);
}

function boolval($bool) {
    if ($bool == null || $bool === false)
        return false;

    if ($bool === true)
        return true;
    
    switch ($bool) {
    case 'True':
    case 'true':
        return true;
    case 'False':
    case 'false':
        return false;
        
    default:
        return !!$bool;
    }
}

function capitalize($s) {
    return strtoupper($s[0]).strtolower(substring($s, 1));
}

function listdir($cwd) {
    $dir = [];
    foreach (scandir($cwd) as $file) {
        switch ($file) {
            case '.':
            case '..':
                break;
            default:
                if (is_dir($cwd . DIRECTORY_SEPARATOR . $file))
                    $dir[] = $file;
        }
    }
    return $dir;
}
