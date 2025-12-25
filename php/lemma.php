<?php
// ^ *error_log

use function std\array_delete;
use function std\array_insert;

require_once 'init.php';
require_once 'std.php';
if ($_POST) {
	function module_exists(string $module)  {
		$path = module_to_lean($module);
		// Case-insensitive check first (works on both OS)
		if (!file_exists($path)) {
			$tokens = explode('.', $module);
			[$section, $segment] = parseInfixSegments($tokens);
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
				if ($index + 2 < count($tokens))
					// move 'of' to the next position
					array_insert($tokens, $index + 2, 'of');
				$module = implode('.', $tokens);
				$path = module_to_lean($module);
				if (!file_exists($path)) {
					if ($index + 2 < count($tokens)) {
						[$tokens[$index - 1], $tokens[$index + 1]] = [$tokens[$index + 1], $tokens[$index - 1]]; // swap
						$module = implode('.', $tokens);
						$path = module_to_lean($module);
						if (!file_exists($path)) {
							if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[3], $matches))
								$tokens[3] = $matches[1] . $matches[2];
							$module = implode('.', $tokens);
							$path = module_to_lean($module);
							if (!file_exists($path)) {
								# mt
								$first = $segment[0];
								for ($i = 2; $i < count($segment); $i++) {
									# try mt $i
									$segment_ = [...$segment];
									$segment_[0] = Not($segment_[$i]);
									$segment_[$i] = Not($first);
									$path = module_to_lean($segment_, $section);
									if (file_exists($path)) {
										$hit = true;
										$segment = $segment_;
										$module = tokens_to_module($segment, $section);
										break;
									}
								}
								if (! $hit) {
									$segment[1] = ['is'];
									# try mpr.mt
									array_insert($segment, 3, ['of']);
									[$segment[0], $segment[2]] = [Not($segment[2]), Not($segment[0])];
									$module = tokens_to_module($segment, $section);
									$path = module_to_lean($segment, $section);
									if (!file_exists($path)) {
										return;
									}
								}
							}
						}
					}
					else {
						$section = $tokens[0];
						$first = array_slice($tokens, 1, $index - 1);
						$second = array_slice($tokens, $index + 1);
						$module = implode('.', array_merge([$section], $second, ['is'], $first));
						$path = module_to_lean($module);
						if (!file_exists($path)) {
							if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[1], $matches)) {
								$tokens[1] = $matches[1] . $matches[2];
								$tokens[$index] = 'of';
								$module = implode('.', $tokens);
								$path = module_to_lean($module);
								if (!file_exists($path))
									return;
							}
							else {
								# mt
								$module = implode('.', array_merge([$section], Not($second), ['of'], Not($first)));
								$path = module_to_lean($module);
								if (!file_exists($path)) {
									# mp.mt
									$module = implode('.', array_merge([$section], Not($first), ['is'], Not($second)));
									$path = module_to_lean($module);
									if (!file_exists($path)) {
										// mpr.mt
										$module = implode('.', array_merge([$section], Not($second), ['is'], Not($first)));
										$path = module_to_lean($module);
										if (!file_exists($path)) {
											return;
										}
									}
								}
							}
						}
					}
				}
				break;
			default:
				if ($tokens[2] === null) {
					if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[1], $matches))
						$tokens[1] = $matches[1] . $matches[2];
					$module = implode('.', $tokens);
					$path = module_to_lean($module);
					if (!file_exists($path))
						return;
				}
				elseif (count($segment) == 3 && $segment[1] == ['of']) {
					[$segment[0], $segment[2]] = [$segment[2], $segment[0]]; // swap
					$segment[1] = ['is']; 
					$module = tokens_to_module($segment, $section);
					$path = module_to_lean($module);
					if (!file_exists($path))
						return;
				}
				else
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
	$term = "(?:[A-Z][\w'!₀-₉]*|(?:of|is|et|ou|to|eq|ne|gt|lt|ge|le|in|as|dvd|sub|sup)(?=\.))";
	$sections = std\listdir($root = dirname(dirname(__FILE__)) . "/Lemma/");
	$sectionRegex = implode('|', $sections);
	$sectionRegex = str_replace('List', 'List(?!\.Vector)', $sectionRegex); // avoid List.Vector
	$sectionRegex = str_replace('Finset', 'Finset(?!\.Nonempty)', $sectionRegex); // avoid Finset.Nonempty
	$sectionRegex = str_replace('Tensor', 'Tensor(?!\.T\b)', $sectionRegex); // avoid Tensor.T
	$sectionRegex = str_replace('Hyperreal', 'Hyperreal(?!\.Infinite(?:Pos|Neg)?(?!\.)\b)', $sectionRegex); // avoid Hyperreal.Infinite
	$sectionRegex = "(?:$sectionRegex)(?=\.[A-Z])";

	function detect_lemma(&$line)  {
		global $sectionRegex, $term, $open_section, $imports, $sections;
		$offset = 0;
		while (preg_match("/\b($sectionRegex)((?:\.$term)+)/", $line, $matches, PREG_OFFSET_CAPTURE, $offset)) {
			if (!in_array($matches[1][0], $open_section))
				$open_section[] = $matches[1][0];

			$module = module_exists($matches[0][0]);
			if ($module && !in_array($module = "Lemma." . $module, $imports))
				$imports[] = $module;

			$line_ = preg_replace("/\b(?<!@)($sectionRegex)\.(?=$term)/", '', $line);
			$offset = $matches[0][1] + strlen($matches[0][0]) - (strlen($line) - strlen($line_));
			$line = $line_;
		}

		if ($matches = std\matchAll("/\b(?!$sectionRegex)($term(?:\.$term)*)((?:\.[a-z_]+)*)(?=\b[^.]|$)/", $line)) {
			foreach ($matches as [, [$lemmaName], [$submodule]]) {
				if ($submodule == '.symm' && $lemmaName == 'Eq')
					continue;
				$lemmaNameReg = str_replace('.','\.', $lemmaName);
				if (array_filter($imports, fn ($import) => preg_match("/^Lemma\.(\w+)\.$lemmaNameReg$/", $import)))
					continue;
				$exists = [];
				foreach ($sections as $section) {
					$module = $section . '.' . $lemmaName;
					if ($module = module_exists($module)) {
						$module = 'Lemma.' . $module;
						$exists[] = [in_array($module, $imports), $section, $module];
					}
				}
				if ($exists) {
					$break = false;
					foreach ($exists as [$hit, $section, $module]) {
						if ($hit) {
							if (!in_array($section, $open_section))
								$open_section[] = $section;
							$break = true;
							break;
						}
					}
					if ($break)
						continue;
					foreach ($exists as [, $section, $module]) {
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

		$explicit = $lemma["explicit"] ?? '';
		if ($explicit) {
			$declspec[] = "-- given";
			$declspec[] = preg_replace("/^/m", '  ', $explicit);
		}
		
		$given = $lemma["given"] ?? '';
		if ($given) {
			if (!$explicit)
				$declspec[] = "-- given";
			$given = array_map(fn($line) => preg_replace("/^/m", '  ', $line), $given);
			array_push($declspec, ...$given);
		}

		$default = $lemma["default"] ?? '';
		if ($default) {
			if (!$explicit && !$given)
				$declspec[] = "-- given";
			$declspec[] = preg_replace("/^/m", '  ', $default);
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
		if ($declspec) {
			$declspec = rtrim($declspec);
			$declspec = "\n$declspec";
		}
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
	function try_pattern($tokens, $lemmaCode) {
		if (is_array($tokens[0]))
			$import = tokens_to_module($tokens, null);
		else 
			$import = implode('.', $tokens);
		$import = str_replace('.', '\.', $import) . "(?!\.(of\.|[A-Z][\w'!₀-₉]*))";
		if (preg_match("/\b$import\b/", $lemmaCode))
			return true;
	};
	$imports = array_filter($imports, function ($import) use ($lemmaCode, $open_section) {
		$tokens = explode('.', $import);
		switch ($tokens[0]) {
		case 'Lemma':
			array_shift($tokens);
			if (in_array($section = $tokens[0], $open_section))
				array_shift($tokens);
			break;
		case 'sympy':
			if ($tokens[1] == 'Basic')
				return;
		case 'stdlib':
		case 'Mathlib':
			return true;
		}
		if (try_pattern($tokens, $lemmaCode))
			return true;
		[$section, $segment] = parseInfixSegments($tokens, $section);
		switch ($tokens[1]) {
		case 'eq':
		case 'as':
		case 'ne':
			[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
			if (try_pattern($tokens, $lemmaCode))
				return true;
			break;
		case 'is':
			$indexOf = array_search('of', $tokens);
			if ($indexOf !== false) {
				$tokens[1] = 'of';
				array_delete($tokens, $indexOf);
				# try mpr:
				if (try_pattern($tokens, $lemmaCode))
					return true;
				# try mp:
				[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
				if (try_pattern($tokens, $lemmaCode))
					return true;
				# try comm:
				if (preg_match("/^([SH]?Eq|Iff)(?!_)(.+)/", $tokens[0], $matches)) {
					$tokens[0] = $matches[1] . "_" . $matches[2];
					if (try_pattern($tokens, $lemmaCode))
						return true;
				}
				if ($indexOf == 3) {
					$tokens[0] = Not($tokens[0]);
					$tokens[2] = Not($tokens[2]);
					if (try_pattern($tokens, $lemmaCode))
						return true;
					[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
					if (try_pattern($tokens, $lemmaCode))
						return true;
				}
			}
			else {
				# try mp:
				$tokens[1] = 'of';
				if (try_pattern($tokens, $lemmaCode))
					return true;
				# try mpr:
				[$tokens[0], $tokens[2]] = [$tokens[2], $tokens[0]]; // swap
				if (try_pattern($tokens, $lemmaCode))
					return true;
				if (count($tokens) == 3) {
					$tokens_ = [...$tokens];
					# try mpr.mt
					$tokens_[0] = Not($tokens_[0]);
					$tokens_[2] = Not($tokens_[2]);
					if (try_pattern($tokens_, $lemmaCode))
						return true;
					// try mp.mt
					[$tokens_[0], $tokens_[2]] = [$tokens_[2], $tokens_[0]]; // swap
					if (try_pattern($tokens_, $lemmaCode))
						return true;
				}
				# try comm:
				$tokens[1] = 'is';
				if (try_pattern($tokens, $lemmaCode))
					return true;
			}
			break;
		case 'of':
			# try comm:
			$tokens_ = [...$tokens];
			if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens_[0], $matches))
				$tokens_[0] = $matches[1] . $matches[2];
			elseif (preg_match("/^([SH]?Eq|Iff)(.+)/", $tokens_[0], $matches))
				$tokens_[0] = $matches[1] . "_" . $matches[2];
			else
				$tokens_ = [];
			if ($tokens_) {
				if (try_pattern($tokens_, $lemmaCode))
					return true;
			}
			# try mt:
			for ($i = 2 ; $i < count($tokens); $i++) {
				$tokens_copy = array_slice($tokens, 2);
				$tokens_copy[$i - 2] = Not($tokens[0]);
				if (try_pattern([Not($tokens[$i]), 'of', ...$tokens_copy], $lemmaCode))
					return true;
			}
			break;
		default:
			if ($tokens[1] === null) {
				# try comm:
				if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[0], $matches))
					$tokens[0] = $matches[1] . $matches[2];
				elseif (preg_match("/^([SH]?Eq|Iff)(.+)/", $tokens[0], $matches))
					$tokens[0] = $matches[1] . "_" . $matches[2];
				else
					break;
				if (try_pattern($tokens, $lemmaCode))
					return true;
			}
			elseif (count($segment) == 3 && $segment[1] == ['is']) {
				[$segment[0], $segment[2]] = [$segment[2], $segment[0]]; // swap
				$segment[1] = ['of']; 
				if (try_pattern($segment, $lemmaCode))
					return true;
			}
			else
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
	$imports = array_unique($imports);
	sort($imports);
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
			std\createNewFile($leanEchoFile, false);
	}
}

if (!$code || !$code['lemma'] || !$code['date']) {
	function contains_module(string $parentModule, string $module): bool {
		$filePath = module_to_path($parentModule, '') . ".lean";
		if (!file_exists($filePath))
			return false;
		$fileObject = new SplFileObject($filePath, 'r');
		// Iterate through the file line by line
		foreach ($fileObject as $line) {
			// preg_match returns 1 if pattern matches, 0 if not, false on error
			$line = rtrim($line);
			if (str_starts_with($line, 'import')) {
				$m = substr($line, strlen('import '));
				if ($m == $module)
					return true;
				if (contains_module($m, $module))
					return true;
			}
			else 
				break;
		}
		return false;
	}

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
				$imports = $code['imports'];
				$hit = false;
				foreach ($imports as $module) {
					if (contains_module($module, $import)) {
						$hit = true;
						break;
					}
				}
				if ($hit)
					return false;
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
		case '≃':
			$modify |= $import_syntax('stdlib.SEq');
			break;
		case 'softmax':
			$modify |= $import_syntax('sympy.tensor.functions');
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