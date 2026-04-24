<?php
// find py/Lemma -type f -name '*.py' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}'

assert(DIRECTORY_SEPARATOR == '/');
$cmd = "find Lemma -type f -name '*.lean' -not -name '*.echo.lean' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}'";

error_log("cmd = $cmd");
exec($cmd, $output_array, $ret);
$result = implode("\n", $output_array);
error_log("result = $result");
echo implode("\n", $output_array);

