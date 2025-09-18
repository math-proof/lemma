<?php
// find py/Lemma -type f -name '*.py' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}'

if (DIRECTORY_SEPARATOR == '/') {
    $cmd = "find Lemma -type f -name '*.lean' -not -name '*.echo.lean' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}'";
}
else {
    $args = "-src " . escapeshellarg($old) . " -dst ". escapeshellarg($new);
    $cmd = "powershell -ExecutionPolicy Bypass -NoProfile -File ".  escapeshellarg("ps1\\rename.ps1") . " -ArgumentList $args";;
}

error_log("cmd = $cmd");
exec($cmd, $output_array, $ret);
$result = implode("\n", $output_array);
error_log("result = $result");
echo implode("\n", $output_array);

