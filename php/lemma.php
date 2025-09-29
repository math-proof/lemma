<?php
// ^ *error_log
require_once 'init.php';
require_once 'std.php';
if ($_POST) {
	function module_exists(string $module)  {
		$path = module_to_lean($module);
		// Case-insensitive check first (works on both OS)
		if (!file_exists($path)) {
			$tokens = explode('.', $module);
			switch ($tokens[2]) {
			case 'eq':
			case 'is':
			case 'as':
				[$tokens[1], $tokens[3]] = [$tokens[3], $tokens[1]]; // swap
				$module = implode('.', $tokens);
				$path = module_to_lean($module);
				if (!file_exists($path))
					return;
				break;
			case 'of':
				$index = 2;
				$tokens[$index] = 'is';
				$module = implode('.', $tokens);
				$path = module_to_lean($module);
				if (!file_exists($path)) {
					$section = $tokens[0];
					$first = array_slice($tokens, 1, $index - 1);
					$second = array_slice($tokens, $index + 1);
					$tokens = array_merge([$section], $second, ['is'], $first);
					$module = implode('.', $tokens);
					$path = module_to_lean($module);
					if (!file_exists($path))
						return;
				}
				break;
			default:
				return;
			}
		}
	
		// Linux (and case-sensitive macOS): Use built-in check
		if (!std\is_linux()) {
			// Windows: Verify exact case via directory scan
			$dir = pathinfo($path, PATHINFO_DIRNAME);
			$file = pathinfo($path, PATHINFO_BASENAME);
			$items = @scandir($dir);
			if (($items === false) || !in_array($file, $items, true))
				return;
		}
		return $module;
	}

	$term = "(?:[A-Z][\w']*|(?:of|is|et|ou|or|and||to|eq|ne|gt|lt|ge|le|in|as|dvd|sub|sup|subset|supset|mod)(?=\.))";
	$sections = std\listdir($root = dirname(dirname(__FILE__)) . "/Lemma/");
	$sectionRegex = implode('|', $sections);
	$sectionRegex = "(?:$sectionRegex)(?=\.[A-Z])";

	function detect_lemma(&$line)  {
		global $sectionRegex, $term, $open_section, $imports, $sections;
		while (preg_match("/\b($sectionRegex)((?:\.$term)+)/", $line, $matches)) {
			if (!in_array($matches[1], $open_section))
				$open_section[] = $matches[1];

			$module = module_exists($matches[0]);
			if ($module && !in_array($module = "Lemma." . $module, $imports))
				$imports[] = $module;

			$line = preg_replace("/\b($sectionRegex)\.(?=$term)/", '', $line);
		}

		if ($matches = std\matchAll("/\b(?!$sectionRegex)($term(?:\.$term)*)((?:\.[a-z_]+)*)(?=\b[^.]|$)/", $line)) {
			foreach ($matches as [, [$lemmaName], [$submodule]]) {
				if ($submodule == '.symm' && $lemmaName == 'Eq')
					continue;
				$lemmaNameReg = str_replace('.','\.', $lemmaName);
				if (array_filter($imports, fn ($import) => preg_match("/^Lemma\.(\w+)\.$lemmaNameReg$/", $import)))
					continue;
				foreach ([...$open_section, ...$sections] as $section) {
					$module = $section . '.' . $lemmaName;
					if ($module = module_exists($module)) {
						$module = 'Lemma.' . $module;
						if (!in_array($module, $imports))
							$imports[] = $module;
						if (!in_array($section, $open_section))
							$open_section[] = $section;
						break;
					}
				}
			}
		}
	}
	$leanCode = [];
	$imports = std\decode($_POST['imports']);
	if (is_string($imports))
		$imports = [$imports];
	$open = std\decode($_POST['open']);
	$open_section = [];
	$open_mathlib = [];
	$open_variable = [];
	if ($open) {
		foreach ($open as $packages) {
			if (std\is_list($packages)) {
				foreach ($packages as $package) {
					if (in_array($package, $sections))
						$open_section[] = $package;
					elseif ($package)
						$open_mathlib[] = $package;
				}
			} else
				$open_variable[] = $packages;
		}
	}

	$set_option = std\decode($_POST['set_option']);
	$def = $_POST['def'];
	if (is_string($def))
		$def = std\decode($def);
	if ($def)
		$def = "\n\n" . implode("\n\n\n", $def);

	$lemmaCode = [];
	foreach ($_POST['lemma'] as $lemma) {
		if ($comment = $lemma['comment'] ?? '')
			$comment = "/--\n$comment\n-/\n";

		if ($attribute = $lemma['attribute'] ?? null) {
			$attribute = std\decode($attribute);
			$attribute = '@[' . implode(", ", $attribute) . "]\n";
		} else
			$attribute = "";

		if ($accessibility = $lemma["accessibility"] ?? null)
			$accessibility = "$accessibility ";
		else
			$accessibility = "";

		$name = $lemma["name"];
		$declspec = [];
		$instImplicit = $lemma["instImplicit"] ?? '';
		if ($instImplicit)
			$declspec[] = preg_replace("/^/m", '  ', $instImplicit);

		$implicit = $lemma["implicit"] ?? '';
		if ($implicit)
			$declspec[] = preg_replace("/^/m", '  ', $implicit);

		$given = $lemma["given"] ?? '';
		if ($given) {
			$declspec[] = "-- given";
			$given = array_map(fn($line) => preg_replace("/^/m", '  ', $line), $given);
			array_push($declspec, ...$given);
		}

		$explicit = $lemma["explicit"] ?? '';
		if ($explicit) {
			if (!$given)
				$declspec[] = "-- given";
			$declspec[] = preg_replace("/^/m", '  ', $explicit);
		}

		$declspec = implode("\n", $declspec);

		$imply = preg_replace("/^/m", '  ', $lemma["imply"]);
		detect_lemma($imply);

		$proof = $lemma['proof'];
		$by = $proof['by'] ? 'by' : ($proof['calc'] ? 'calc' : '');
		if ($by)
			$proof = $proof[$by];

		foreach ($proof as &$line)
			detect_lemma($line);
		$proof = array_map(fn($line) => preg_replace("/^/m", '  ', $line), $proof);
		$proof = ltrim(implode("\n", $proof), "\n");
		$proof = rtrim($proof);
		$proof = preg_replace("/(?<=\n)\s+\n/", '', $proof);
		if ($declspec)
			$declspec = "\n$declspec";
		if (!str_ends_with($declspec, ':')) 
			$declspec .= " :";
		$proof = <<<EOT
$comment$attribute{$accessibility}lemma $name$declspec
-- imply
$imply
-- proof
$proof
EOT;
		$lemmaCode[] = $proof;
	}
	$lemmaCode = implode("\n\n\n", $lemmaCode);
	$imports = array_filter($imports, function ($import) use ($lemmaCode, $open_section) {
		$tokens = explode('.', $import);
		switch ($tokens[0]) {
		case 'Lemma':
			array_shift($tokens);
			if (in_array($tokens[0], $open_section))
				array_shift($tokens);
			$import = implode('.', $tokens);
			break;
		case 'sympy':
		case 'stdlib':
		case 'Mathlib':
			return true;
		}
		$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w']*))";
		if (preg_match("/\b$import\b/", $lemmaCode))
			return true;
		switch ($tokens[1]) {
		case 'eq':
		case 'as':
		case 'ne':
			[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
			$import = implode('.', $tokens);
			$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w']*))";
			if (preg_match("/\b$import\b/", $lemmaCode))
				return true;
			break;
		case 'is':
			# try mp:
			$tokens[1] = 'of';
			$import = implode('.', $tokens);
			$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w']*))";
			if (preg_match("/\b$import\b/", $lemmaCode))
				return true;
			# try mpr:
			[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
			$import = implode('.', $tokens);
			$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w']*))";
			if (preg_match("/\b$import\b/", $lemmaCode))
				return true;
			# try comm:
			$tokens[1] = 'is';
			$import = implode('.', $tokens);
			$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w']*))";
			if (preg_match("/\b$import\b/", $lemmaCode))
				return true;
			break;
		default:
			return;
		}
	});
	if (!array_filter($imports, fn($import) => str_starts_with($import, 'Lemma.')) && array_search('sympy.Basic', $imports) === false)
		$imports[] = "sympy.Basic";

	$open_section = array_reduce($imports, function ($carry, $import)  {
		$module = explode('.', $import);
		if ($module[0] == 'Lemma')
			$carry[$module[1]] = true;
		return $carry;
	}, []);
	$imports = array_map(fn($import) => "import $import", $imports);
	// find Lemma -name "*.lean" -exec perl -i -0777 -pe 's/(\S+)(?=\n\n@\[\w+)/$1\n/g' {} +
	// find Lemma -name "*.lean" -exec perl -i -0777 -pe 's/((\S+)\n+)(?=\n\n\n-- created)/$2/g' {} +
	$leanCode[] = implode("\n", $imports);

	$open_section = array_keys($open_section);
	$open_section = array_merge($open_section, $open_mathlib);
	if ($open_section)
		$leanCode[] = "open " . implode(" ", $open_section);
	foreach ($open_variable as $entity) {
		[[$section, $variables]] = std\entries($entity);
		$variables = implode(" ", $variables);
		$leanCode[] = "open $section ($variables)";
	}

	if ($set_option) {
		foreach ($set_option as $option) {
			if (std\is_list($option))
				$leanCode[] = "set_option " . implode(" ", $option);
		}
	}

	if ($def)
		$leanCode[] = $def;

	$leanCode[] = "\n\n" . $lemmaCode;

	$date = std\decode($_POST['date']);
	$created = $date['created'];

	$leanCode[] = "\n\n-- created on $created";

	$updated = date('Y-m-d');
	if ($updated != $created)
		$leanCode[] = "-- updated on $updated";

	$leanCode[] = "";

	$leanCode = array_map(fn($line) => str_replace("\r", '', $line), $leanCode);
	$file = new std\Text($leanFile);
	$file->writelines($leanCode);
}

$code = null;
$leanEchoFile = preg_replace('/\.lean$/', '.echo.lean', $leanFile);

if (!file_exists($leanEchoFile) || filemtime($leanFile) < filemtime($leanEchoFile)) {
	$code = fetch_from_mysql(get_project_name(), $module);
	if ($code) {
		$code['imports'] = std\decode($code['imports']);
		$code['open'] = std\decode($code['open']);
		$code['def'] = std\decode($code['def']);
		$code['lemma'] = std\decode($code['lemma']);
		$code['error'] = std\decode($code['error']);
		$code['date'] = std\decode($code['date']);
		if (!file_exists($leanEchoFile))
			std\createNewFile($leanEchoFile);
	}
}

if (!$code || !$code['lemma'] || !$code['date']) {
	// $_ = new std\Timer("compile and render2vue");
	$leanCode = compile(file_get_contents($leanFile));
	$syntax = [];
	$code = $leanCode->render2vue(false, $modify, $syntax);
	$import_syntax = function ($import) use ($leanCode, $code) {
		if (!in_array($import, $imports = $code['imports'])) {
			$prefix = "Lemma.";
			$imports = array_filter($imports, fn($module) => str_starts_with($module, $prefix));
			$imports = [...$imports];
			$offset = strlen($prefix);
			$imports = array_map(fn($module) => substr($module, $offset), $imports);
			$imports = std\encode($imports);
			$imports = mysql\mysqlStr($imports);
			$sql = <<<EOF
WITH RECURSIVE dependencies AS (
	select 
		* 
	from 
		json_table(
			$imports,
			'$[*]' columns(module text path '$')
		) as jt
	UNION ALL
	SELECT
		SUBSTRING(jt.module, LOCATE('.', jt.module) + 1)
	FROM
		dependencies
		JOIN axiom.lemma as _t using(module)
		CROSS JOIN JSON_TABLE(
			_t.imports,
			'$[*]' COLUMNS (module text PATH '$')
		) AS jt
	WHERE
		jt.module LIKE 'Lemma.%'
)
select 
    count(*)
from dependencies 
    JOIN axiom.lemma as _t using(module)
    cross join json_table(
        imports,
        '$[*]' columns(module text path '$')
    ) as jt
where 
	jt.module = "$import"
EOF;
			[[$count]] = get_rows($sql, MYSQLI_NUM);
			if (!intval($count)) {
				array_unshift($code['imports'], $import);
				$leanCode->import($import);
				return true;
			}
		}
		return false;
	};

	foreach ($syntax as $tac => $_) {
		switch ($tac) {
		case 'denote':
			$modify |= $import_syntax('sympy.core.relational');
			break;
		case 'mp':
		case 'mpr':
			$modify |= $import_syntax('sympy.core.logic');
			break;
		case '²':
		case '³':
		case '⁴':
			$modify |= $import_syntax('sympy.core.power');
			break;
		case 'Ici':
		case 'Iic':
		case 'Ioi':
		case 'Iio':
		case 'Ioc':
		case 'Ioo':
		case 'Icc':
		case 'Ico':
		case 'range':
			$modify |= $import_syntax('sympy.sets.sets');
			break;
		case 'setOf':
			$modify |= $import_syntax('sympy.concrete.quantifier');
			break;
		case 'LeanStack':
			$modify |= $import_syntax('sympy.tensor.stack');
			break;
		case 'Tensor':
			if (array_search('sympy.tensor.tensor', $code['imports']) === false && 
				array_search('sympy.tensor.stack', $code['imports']) === false)
				$modify |= $import_syntax('sympy.tensor.Basic');
			break;
		case 'IntegerRing':
			$modify |= $import_syntax('sympy.polys.domains');
			break;
		case 'KroneckerDelta':
			$modify |= $import_syntax('sympy.functions.special.tensor_functions');
			break;
		case 'eye':
			$modify |= $import_syntax('sympy.matrices.expressions.special');
			break;
		}
	}
	if ($modify) {
		$file = new std\Text($leanFile);
		$file->write("$leanCode");
	}
}
?>

<title><?php echo $title; ?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<link rel=stylesheet href="static/unpkg.com/prismjs@1.30.0/themes/prism.min.css" />
<body></body>
<?php
include_once 'script.php';
?>
<script src="static/unpkg.com/lz-string@1.5.0/libs/lz-string.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script src="static/unpkg.com/prismjs@1.30.0/prism.js"></script>
<script src="static/unpkg.com/prismjs@1.30.0/components/prism-lean.js"></script>
<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as lean from "./static/codemirror/mode/lean/lean.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"
import * as comment from "./static/codemirror/addon/comment/comment.js"

createApp('render', <?php echo std\encode($code) ?>);

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>