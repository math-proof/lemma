<title>summary</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'init.php';

function section($axiom)
{
    [$section] = explode('.', $axiom, 2);
    return $section;
}

$repertoire = [];
$user = get_project_name();
foreach (select_lemma_by_error($user) as $tuple) {
    [$axiom, $type] = $tuple;
    $repertoire[section($axiom)][$type][] = $axiom;
}

$state_count_pairs = [];
$_t_type = _t_type($user); 
$_t_matrix = _t_matrix($user);
$sql = <<<EOT
with $_t_type, $_t_matrix
select 
    _t_type.type,
    count(distinct _t_matrix.module) as count
from 
    _t_type
    join _t_matrix using (type)
group by
    type
EOT;

foreach (get_rows($sql, MYSQLI_ASSOC) as $res) {
    $state_count_pairs[] = $res;
}


$state_count_pairs[] = [
    'type' => 'total',
    'count' => select_count($user)
];

include_once 'script.php';
?>

<script type=module>
createApp('axiomSummary', {
    state_count_pairs : <?php echo std\encode($state_count_pairs)?>,
    repertoire : <?php echo std\encode($repertoire)?>,
});

</script>
