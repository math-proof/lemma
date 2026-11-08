<?php
require_once 'php/utility.php';
require_once 'php/mysql.php';
$user = get_user();
echo "user=$user\n";
foreach (get_rows("select axiom, state, char_length(latex) as llen from axiom where user='$user' and axiom like '%DetBlock_Stack_MulPowS%'") as $r) {
    echo json_encode($r, JSON_UNESCAPED_UNICODE), "\n";
}
echo "--- sample Matrix any ---\n";
foreach (get_rows("select axiom, state from axiom where user='$user' and axiom like 'Matrix.%' limit 10") as $r) {
    echo json_encode($r, JSON_UNESCAPED_UNICODE), "\n";
}
