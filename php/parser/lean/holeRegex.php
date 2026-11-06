<?php
/**
 * holeRegex helpers (Body t366) — polymorphic Node::holeRegex composition.
 * Mirrors js/parser/lean/pathChoices.js holeRegex* exports.
 * Plural MulS alt stays in lemmaPath, not here.
 */

function escapeHoleReLit($s) {
    return preg_replace('/[.*+?^${}()|[\]\\\\]/', '\\\\$0', (string)$s);
}

function wrapHoleOpt($filled) {
    if ($filled === null || $filled === '') return '_';
    return '(_|' . $filled . ')';
}

function holeRegexDefaultNameToken($text) {
    if (!$text) return '';
    $s = (string)$text;
    if (str_contains($s, '.')) $s = substr($s, strrpos($s, '.') + 1);
    if ($s === '' || $s === '_' || $s === '[anonymous]' || $s === 'anonymous') return '';
    if (str_contains($s, '_')) {
        $parts = explode('_', $s);
        $s = '';
        foreach ($parts as $p) {
            if ($p === '') continue;
            $s .= strtoupper($p[0]) . substr($p, 1);
        }
    } else {
        $s = strtoupper($s[0]) . substr($s, 1);
    }
    return preg_replace('/[^\x00-\x7F]+/', '', preg_replace('/\*+$/', '', $s));
}

function holeRegexChild($node, $opts = []) {
    if (!$node || !is_object($node) || !method_exists($node, 'holeRegex')) return null;
    $frag = $node->holeRegex($opts);
    return ($frag === null || $frag === '') ? null : $frag;
}

function holeRegexPeelParen($n) {
    $x = $n;
    for ($i = 0; $i < 6 && $x; $i++) {
        if ($x instanceof LeanParenthesis) {
            $x = $x->arg;
            continue;
        }
        break;
    }
    return $x;
}

function holeRegexIsSqrtNode($n) {
    $x = holeRegexPeelParen($n);
    if (!$x) return false;
    if ($x instanceof Lean_sqrt) return true;
    if ($x instanceof LeanProperty) {
        $p = $x->rhs;
        return ($p->text ?? '') === 'sqrt';
    }
    return false;
}

function holeRegexIsDivNode($n) {
    $x = holeRegexPeelParen($n);
    return $x instanceof LeanDiv;
}

function holeRegexCombineArith($tag, $leftNode, $rightNode, $opts = [], $mul = null) {
    $L = holeRegexChild($leftNode, $opts);
    $R = $rightNode !== null ? holeRegexChild($rightNode, $opts) : null;
    $lHole = ($L === null || $L === '');
    $rHole = ($R === null || $R === '');
    $isMul = is_array($mul) && !empty($mul['isMul']);
    if (!$lHole && !$rHole) {
        if ($isMul && holeRegexIsSqrtNode($leftNode) && holeRegexIsDivNode($rightNode))
            return $tag . wrapHoleOpt($L) . '_' . wrapHoleOpt($R);
        return $tag . wrapHoleOpt($L) . wrapHoleOpt($R);
    }
    if (!$lHole && $rHole) {
        if ($isMul && preg_match('/^(?:T|Adjoint|Conj)$/', $L)) return $tag . $L . '__';
        if (preg_match('/^-?\d+$/', $L)) return $tag . wrapHoleOpt($L) . '_';
        if (preg_match('/[(|]/', $L)) return $tag . wrapHoleOpt($L) . '_';
        return $tag . $L;
    }
    if ($lHole && !$rHole) return $tag . '_' . wrapHoleOpt($R);
    if ($isMul && (($mul['subscript'] ?? '') === 'ᵥ')) return $tag . '__';
    if ($isMul) return !empty($opts['mulBothHolesBare']) ? $tag : ($tag . '(_)' . '(_)');
    return $tag;
}

function holeRegexCombineRel($tag, $leftNode, $rightNode, $opts = []) {
    $L = holeRegexChild($leftNode, $opts);
    $R = holeRegexChild($rightNode, $opts);
    $lHole = ($L === null || $L === '');
    $rHole = ($R === null || $R === '');
    if ($lHole && !$rHole) return $tag . '_' . wrapHoleOpt($R);
    if (!$lHole && $rHole) return $tag . wrapHoleOpt($L);
    if (!$lHole && !$rHole) return $tag . wrapHoleOpt($L) . wrapHoleOpt($R);
    return $tag;
}

function holeRegexCombineUnary($tag, $argNode, $opts = []) {
    $inner = holeRegexChild($argNode, $opts);
    if ($inner === null || $inner === '') return $tag;
    return $tag . wrapHoleOpt($inner);
}
