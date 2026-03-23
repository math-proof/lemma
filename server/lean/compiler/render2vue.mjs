/**
 * Port of `LeanModule::render2vue` / `merge_proof` (php/parser/lean.php ~4685–5188).
 * Produces the same JSON shape as the PHP `LeanModule::render2vue`.
 */

import {
    compile,
    LeanModule,
    Lean_lemma,
    Lean_def,
    LeanToken,
    LeanColon,
    LeanAssign,
    LeanBy,
    LeanCaret,
    LeanLineComment,
    LeanParenthesis,
    LeanTactic,
    LeanArgsSpaceSeparated,
    LeanArgsNewLineSeparated,
    LeanProperty,
} from '../../../static/js/parser/lean.js';
import { escapeLatexText } from '../parseLeanStub.mjs';


/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function nameOf(node) {
    return node && node.constructor && node.constructor.name;
}

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function strStmt(node) {
    return String(node).replace(/\n$/, '');
}

/** Normalize import path: trim, collapse space-around-dot to dot, then spaces to dots to match PHP. */
function normalizeImportStr(s) {
    return s.trim().replace(/\s*\.\s*/g, '.').replace(/\s+/g, '.');
}

/** Normalize type string: collapse spaces, fix bracket interior spacing to match Lean source e.g. [n, n]. */
function normalizeTypeStr(s) {
    return s
        .trim()
        .replace(/\s+/g, ' ')
        .replace(/\[\s+/g, '[')
        .replace(/\s+\]/g, ']');
}

/** PHP `preg_replace("/^  /m", "", …)` */
function unindentTwo(s) {
    return s.replace(/^  /gm, '');
}

/** Normalize instImplicit to match PHP: "[NeZero (l : ℕ)]" not "[ NeZero ( l  ℕ)]". */
function normalizeInstImplicit(s) {
    if (!s || !s.trim()) return s;
    return s
        .split('\n')
        .map((line) =>
            line
                .trim()
                .replace(/\s{2,}/g, ' ')
                .replace(/\[\s+/g, '[')
                .replace(/\s+\]/g, ']')
                .replace(/\(\s+/g, '(')
                .replace(/\s+\)/g, ')'),
        )
        .join('\n');
}

/**
 * Extract attribute names from LeanAttribute (e.g. @[main] → ['main']).
 * Handles both LeanBracket and LeanArgsSpaceSeparated (from push_left).
 */
function extractAttribute(attr) {
    if (!attr) return null;
    let a = /** @type {*} */ (attr).arg;
    if (nameOf(a) === 'LeanArgsSpaceSeparated') {
        const bracket = a.args.find((x) => nameOf(x) === 'LeanBracket');
        a = bracket || null;
    }
    if (!a || nameOf(a) !== 'LeanBracket') return null;
    a = /** @type {*} */ (a).arg;
    if (a instanceof LeanArgsSpaceSeparated)
        return a.args.map((x) => strStmt(x)).filter(Boolean);
    if (a instanceof LeanToken) return [strStmt(a)];
    return null;
}

/**
 * PHP `escape_specials` (php/parser/lean.php ~9331–9341).
 * @param {string} token
 */
function escapeSpecials(token) {
    return token.replace(/^(\w+?)_(.+)/, (_m, head, tail) => {
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        return head.length === 1 ? `${head}_{${escTail}}` : `${head}\\_${escTail}`;
    });
}

/**
 * PHP `latex_tag` (php/parser/lean.php ~9344–9352).
 * @param {string} tag
 */
function latexTag(tag) {
    return tag
        .split('.')
        .map((t) => escapeSpecials(t))
        .join('.');
}

/**
 * PHP `std\setitem` via path segments (last segment is the value).
 * @param {Record<string, unknown>} data
 * @param {string[]} segs
 */
function setItemFromPath(data, segs) {
    if (segs.length === 1) {
        data[segs[0]] = segs[0];
        return;
    }
    const value = segs[segs.length - 1];
    const keys = segs.slice(0, -1);
    /** @type {Record<string, unknown>} */
    let cur = data;
    for (let i = 0; i < keys.length; i++) {
        const k = keys[i];
        if (i === keys.length - 1) {
            cur[k] = value;
            return;
        }
        if (cur[k] == null || typeof cur[k] !== 'object') cur[k] = {};
        cur = /** @type {Record<string, unknown>} */ (cur[k]);
    }
}

/**
 * PHP `LeanModule::array_push` (php/parser/lean.php ~4867–4877).
 * @param {unknown[][]} vars
 * @param {import('../../../static/js/parser/lean.js').Lean} lhs
 * @param {import('../../../static/js/parser/lean.js').Lean} rhs
 */
function arrayPushVars(vars, lhs, rhs) {
    if (lhs instanceof LeanToken) {
        /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
        let args = [lhs, rhs];
        while (args.length && nameOf(args[args.length - 1]) === 'Lean_rightarrow') {
            const end = args[args.length - 1];
            args.splice(args.length - 1, 1, /** @type {*} */ (end).lhs, /** @type {*} */ (end).rhs);
        }
        vars.push(args);
    } else if (lhs instanceof LeanArgsSpaceSeparated) {
        for (const sub of lhs.args) arrayPushVars(vars, sub, rhs);
    }
}

/**
 * @param {unknown[]} implicit
 */
function parseVars(implicit) {
    const vars = [];
    for (const brace of implicit) {
        if (nameOf(brace) === 'LeanBrace') {
            const colon = /** @type {*} */ (brace).arg;
            if (colon instanceof LeanColon) arrayPushVars(vars, colon.lhs, colon.rhs);
        }
    }
    /** @type {Record<string, unknown>} */
    const kwargs = {};
    for (const v of vars) {
        const segs = v.map((a) => strStmt(a));
        setItemFromPath(kwargs, segs);
    }
    return kwargs;
}

/**
 * PHP `std\zipped` for two arrays (php/std.php ~1856+).
 * @template T, U
 * @param {T[]} a
 * @param {U[]} b
 * @returns {[T, U][]}
 */
function zipped(a, b) {
    const n = Math.min(a.length, b.length);
    /** @type {[T, U][]} */
    const out = [];
    for (let i = 0; i < n; ++i) out.push([a[i], b[i]]);
    return out;
}

/**
 * Build a map from let-binding names to their RHS AST nodes.
 * Used to expand `_` holes in denote tactics (e.g. denote h_Ξ_def : Ξ = _).
 * @param {import('../../../static/js/parser/lean.js').Lean[]} implyStmts
 * @returns {Record<string, import('../../../static/js/parser/lean.js').Lean>}
 */
function buildLetBindings(implyStmts) {
    const bindings = {};
    if (!implyStmts?.length) return bindings;
    for (const stmt of implyStmts) {
        if (nameOf(stmt) !== 'Lean_let' && nameOf(stmt) !== 'Lean_have') continue;
        const arg = stmt.arg;
        if (!arg) continue;
        let nameNode = null;
        let rhsNode = null;
        if (arg instanceof LeanAssign) {
            if (arg.lhs instanceof LeanColon) {
                nameNode = arg.lhs.lhs;
                rhsNode = arg.rhs;
            } else {
                nameNode = arg.lhs;
                rhsNode = arg.rhs;
            }
        } else if (arg instanceof LeanColon && arg.rhs instanceof LeanAssign) {
            nameNode = arg.rhs?.lhs;
            rhsNode = arg.rhs?.rhs;
        }
        if (nameNode && rhsNode) {
            const name = strStmt(nameNode).trim();
            if (name) bindings[name] = rhsNode;
        }
    }
    return bindings;
}

/**
 * Compute LaTeX for a denote tactic when the RHS hole can be expanded from let bindings.
 * E.g. denote h_Ξ_def : Ξ = _ with let Ξ := (1:...).band_part (l-1) (u-1) yields Ξ = 1.band_part ...
 * Handles both LeanColon (denote h_X : Y = _) and LeanTactic(denote) with LeanColon arg.
 * @param {import('../../../static/js/parser/lean.js').Lean} stmt
 * @param {Record<string, unknown>} syntax
 * @returns {string | null}
 */
function denoteLatexFromLetBindings(stmt, syntax) {
    let tag = '';
    let prop = null;
    if (stmt instanceof LeanColon && stmt.lhs && stmt.rhs) {
        prop = stmt.rhs;
        const lhsStr = strStmt(stmt.lhs).trim();
        const m = lhsStr.match(/^denote\s+(.+)$/);
        tag = m ? m[1].trim() : lhsStr;
    } else if (stmt instanceof LeanTactic && stmt.tacticName === 'denote') {
        const arg = stmt.arg;
        if (arg instanceof LeanColon && arg.lhs && arg.rhs) {
            prop = arg.rhs;
            tag = strStmt(arg.lhs).trim().replace(/^denote\s+/, '') || strStmt(arg.lhs).trim();
        }
    }
    if (!prop || !tag) return null;
    const isHole = (n) => {
        if (n instanceof LeanToken && n.text === '_') return true;
        if (n?.args) {
            const nonCaret = n.args.filter((a) => !(a instanceof LeanCaret));
            return nonCaret.length === 1 && nonCaret[0] instanceof LeanToken && nonCaret[0].text === '_';
        }
        return false;
    };
    let lhsNode = null;
    let rhsNode = null;
    if (prop?.lhs != null && prop?.rhs != null) {
        lhsNode = prop.lhs;
        rhsNode = prop.rhs;
    } else if (prop?.args?.length >= 2) {
        lhsNode = prop.args[0];
        rhsNode = prop.args[1];
    }
    if (!lhsNode || !isHole(rhsNode)) return null;
    const letBindings = syntax?.letBindings ?? {};
    const lhsName = strStmt(lhsNode).trim();
    let expansion = letBindings[lhsName];
    if (!expansion && lhsName.endsWith("'")) {
        expansion = letBindings[lhsName.slice(0, -1)];
    }
    if (!expansion || typeof expansion.toLatex !== 'function') return null;
    const lhsLatex = lhsNode.toLatex(syntax);
    const rhsLatex = expansion.toLatex(syntax);
    const taggedTag = escapeLatexText(tag);
    return `${lhsLatex} = ${rhsLatex}\\tag*{\\text{${taggedTag}}}`;
}

/**
 * Port of `LeanModule::merge_proof` (php/parser/lean.php ~4685–4725).
 * When echo is false, computes LaTeX for denote tactics from let bindings (syntax.letBindings).
 * @param {import('../../../static/js/parser/lean.js').LeanArgs} proof
 * @param {boolean} echo
 * @param {Record<string, unknown>} [syntax]
 */
export function mergeProof(proof, echo, syntax = {}) {
    let list = proof.args;
    if (list[0] instanceof LeanLineComment && list[0].text === 'proof') list = list.slice(1);
    list = list.filter((s) => !(s instanceof LeanCaret));
    /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
    const statements = [];
    for (const s of list) statements.push(...s.split(syntax));

    /** @type {[import('../../../static/js/parser/lean.js').Lean[], string | null][]} */
    const code = [];
    /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
    let last = [];

    if (echo) {
        for (const stmt of statements) {
            const echoNode = stmt instanceof LeanTactic ? stmt.getEcho() : undefined;
            if (echoNode) {
                code.push([last, typeof echoNode.line === 'number' ? null : echoNode.line]);
                last = [];
            } else last.push(stmt);
        }
    } else {
        for (const stmt of statements) {
            const isHave = nameOf(stmt) === 'Lean_have';
            if (isHave || stmt instanceof LeanTactic) {
                last.push(stmt);
                code.push([last, null]);
                last = [];
            } else last.push(stmt);
        }
    }
    if (last.length) code.push([last, null]);

    return code.map(([stmts, latex]) => {
        let stepLatex = null;
        if (!echo && !latex) {
            const expanded = stmts
                .map((st) => denoteLatexFromLetBindings(st, syntax))
                .filter(Boolean);
            if (expanded.length === 1) stepLatex = expanded[0];
            else if (expanded.length > 1) stepLatex = `\\begin{gather}\n${expanded.join(' \\\\\n')}\n\\end{gather}`;
            else {
                const fallback = stmts
                    .map((st) => {
                        try {
                            const l = typeof st.toLatex === 'function' ? st.toLatex(syntax) : null;
                            return l && typeof l === 'string' && l.trim() ? l : null;
                        } catch {
                            return null;
                        }
                    })
                    .filter(Boolean);
                if (fallback.length === 1) stepLatex = fallback[0];
                else if (fallback.length > 1) stepLatex = `\\begin{gather}\n${fallback.join(' \\\\\n')}\n\\end{gather}`;
            }
        }
        return {
            lean: unindentTwo(stmts.map((st) => strStmt(st)).join('\n')),
            latex: latex ?? stepLatex,
        };
    });
}

/**
 * Port of `LeanModule::render2vue` (php/parser/lean.php ~4912–5188).
 * @param {LeanModule} mod
 * @param {boolean} echo
 * @param {{ value?: boolean } | null} [modify]
 * @param {Record<string, unknown>} [syntax]
 */
export function render2vue(mod, echo, modify = null, syntax = {}) {
    if (!echo) mod.relocateLastComment();

    /** @type {string[]} */
    const import_ = [];
    /** @type {unknown[]} */
    const open = [];
    /** @type {unknown[]} */
    const set_option = [];
    /** @type {string[]} */
    const def = [];
    /** @type {unknown[]} */
    const lemma = [];
    /** @type {Record<string, string>} */
    const date = {};
    /** @type {unknown[]} */
    const error = [];
    /** @type {string | null} */
    let comment = null;

    const args = mod.args;
    for (let idx = 0; idx < args.length; idx++) {
        const stmt = args[idx];
        if (nameOf(stmt) === 'Lean_import') {
            import_.push(normalizeImportStr(strStmt(/** @type {*} */ (stmt).arg)));
        } else if (stmt instanceof Lean_lemma) {
            /** @type {import('../../../static/js/parser/lean.js').LeanAssign | null} */
            let assignment = stmt.assignment instanceof LeanAssign ? stmt.assignment : null;
            /** @type {number} */
            let assignIdx = -1;
            if (!assignment) {
                let proofStart = args.length;
                for (let k = idx + 1; k < args.length; k++) {
                    const x = args[k];
                    if (x instanceof LeanLineComment && /** @type {*} */ (x).text === 'proof') {
                        proofStart = k;
                        break;
                    }
                    if (x && nameOf(x) === 'LeanTactic') {
                        proofStart = k;
                        break;
                    }
                }
                for (let j = idx + 1; j < proofStart; j++) {
                    const cand = args[j];
                    if (cand instanceof LeanAssign) {
                        const lhs = cand.lhs;
                        if (lhs && (nameOf(lhs) === 'Lean_let' || nameOf(lhs) === 'Lean_have')) continue;
                        assignment = cand;
                        assignIdx = j;
                    }
                }
                if (!assignment) {
                    for (let j = idx + 1; j < args.length; j++) {
                        const cand = args[j];
                        if (cand instanceof LeanAssign) {
                            assignment = cand;
                            assignIdx = j;
                            break;
                        }
                    }
                }
            }
            if (assignment instanceof LeanAssign) {
                const accessibility = stmt.accessibility;
                let declspec = assignment.lhs;
                let flatInstImplicit = [];
                let flatExplicit = '';
                let flatGiven = null;
                /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
                let flatImplyStmts = [];
                if (assignIdx >= 0) {
                    let firstAssign = assignIdx;
                    for (let k = idx + 1; k < assignIdx; k++) {
                        if (args[k] instanceof LeanAssign) {
                            firstAssign = k;
                            break;
                        }
                    }
                    /** Collect Lean_let/Lean_have between lemma and main assignment for imply (JS parser may have them as siblings). */
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (nameOf(s) === 'Lean_let' || nameOf(s) === 'Lean_have') {
                            flatImplyStmts.push(s);
                        }
                    }
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (nameOf(s) === 'LeanBracket') {
                            flatInstImplicit.push(strStmt(s));
                            continue;
                        }
                        /** (A : T) and (V : T) — recurse into LeanArgsSpaceSeparated or handle LeanParenthesis(LeanColon). */
                        const collectParenColons = (/** @type {*} */ n) => {
                            if (!n) return;
                            if (nameOf(n) === 'LeanParenthesis' && n.arg instanceof LeanColon) {
                                const col = n.arg;
                                if (col.lhs && col.rhs) {
                                    if (flatGiven === null) flatGiven = [];
                                    flatGiven.push({
                                        lean: `(${strStmt(col.lhs).trim()} : ${normalizeTypeStr(strStmt(col.rhs))})`,
                                        latex: col.toLatex ? col.toLatex(syntax) : null,
                                    });
                                }
                                return;
                            }
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            for (const child of a) collectParenColons(child);
                        };
                        if (nameOf(s) === 'LeanParenthesis' && s.arg instanceof LeanColon) {
                            collectParenColons(s);
                            continue;
                        }
                        if (nameOf(s) === 'LeanArgsSpaceSeparated' || nameOf(s) === 'LeanArgsNewLineSeparated') {
                            collectParenColons(s);
                            continue;
                        }
                        if (nameOf(s) === 'LeanColon' && s.lhs) {
                            const lb = s.lhs;
                            if (nameOf(lb) === 'LeanBracket') {
                                const inner = /** @type {*} */ (lb).arg;
                                const lhsStr = inner ? strStmt(inner).trim() : strStmt(lb).trim();
                                const rhsStr = s.rhs ? strStmt(s.rhs).trim() : '';
                                const parts = lhsStr.split(/\s+/).filter(Boolean);
                                const varPart = parts.length > 1 ? parts[parts.length - 1] : parts[0] || '';
                                const headPart = parts.length > 1 ? parts.slice(0, -1).join(' ') : lhsStr;
                                const repr =
                                    rhsStr && varPart
                                        ? `[${headPart} (${varPart} : ${rhsStr})]`
                                        : `[${lhsStr}${rhsStr ? ` : ${rhsStr}` : ''}]`;
                                flatInstImplicit.push(repr);
                            } else if (nameOf(lb) === 'LeanParenthesis' || (nameOf(lb) === 'LeanColon' && lb.rhs)) {
                                if (nameOf(s.rhs) === 'LeanStatements' || nameOf(s.rhs) === 'LeanArgsNewLineSeparated') {
                                    const inner = lb;
                                    if (nameOf(inner) === 'LeanColon' && inner.lhs && inner.rhs) {
                                        const innerLhs = inner.lhs;
                                        if (nameOf(innerLhs) === 'LeanParenthesis' && inner.rhs) {
                                            if (flatGiven === null) flatGiven = [];
                                            const varPart = strStmt(
                                                /** @type {*} */ (innerLhs).arg
                                            ).trim();
                                            const typePart = normalizeTypeStr(strStmt(inner.rhs));
                                            flatGiven.push({
                                                lean: `(${varPart} : ${typePart})`,
                                                latex: inner.toLatex ? inner.toLatex(syntax) : null,
                                            });
                                        }
                                    }
                                } else {
                                    if (flatGiven === null) flatGiven = [];
                                    let leanStr;
                                    if (nameOf(lb) === 'LeanParenthesis' && s.rhs) {
                                        const varPart = strStmt(/** @type {*} */ (lb).arg).trim();
                                        const typePart = normalizeTypeStr(strStmt(s.rhs));
                                        leanStr = `(${varPart} : ${typePart})`;
                                    } else {
                                        leanStr = strStmt(s).trim();
                                        if (nameOf(lb) === 'LeanParenthesis' && !leanStr.startsWith('('))
                                            leanStr = '(' + leanStr;
                                    }
                                    if (leanStr.includes('-- imply'))
                                        leanStr = leanStr.replace(/\s*--\s*imply.*$/, '').trim();
                                    flatGiven.push({ lean: leanStr, latex: s.toLatex ? s.toLatex(syntax) : null });
                                }
                            }
                        }
                    }
                    if (flatGiven && flatGiven.length > 0) {
                        const lines = flatGiven.map((g) => g.lean);
                        lines[lines.length - 1] += ' :';
                        flatExplicit = lines.join('\n');
                        flatGiven = null;
                    }
                }
                let useSimpleDeclspec = false;
                if (declspec instanceof LeanColon) {
                    const rhsColon = declspec.rhs;
                    const rhsArgs = rhsColon && 'args' in rhsColon ? /** @type {{ args?: unknown[] }} */ (rhsColon).args : null;
                    const isImplyList =
                        rhsArgs &&
                        Array.isArray(rhsArgs) &&
                        rhsArgs.length > 0 &&
                        (rhsArgs[0] instanceof LeanLineComment ||
                            nameOf(rhsArgs[0]) === 'Lean_let' ||
                            nameOf(rhsColon) === 'LeanArgsSpaceSeparated' ||
                            nameOf(rhsColon) === 'LeanStatements' ||
                            nameOf(rhsColon) === 'LeanArgsNewLineSeparated');
                    if (!rhsColon || !rhsArgs || !isImplyList) {
                        if (
                            assignIdx >= 0 &&
                            assignment.lhs &&
                            (typeof assignment.lhs.toLatex === 'function' || flatImplyStmts.length > 0)
                        ) {
                            useSimpleDeclspec = true;
                        } else {
                            error.push({
                                code: strStmt(declspec),
                                line: 0,
                                info: 'lemma colon rhs must have args (LeanArgsSpaceSeparated)',
                                type: 'linter',
                            });
                            continue;
                        }
                    }
                }
                if (declspec instanceof LeanColon && !useSimpleDeclspec) {
                    const rhsColon = declspec.rhs;
                    let attribute = extractAttribute(stmt.attribute);
                    let imply = /** @type {import('../../../static/js/parser/lean.js').Lean[]} */ (
                        /** @type {{ args: import('../../../static/js/parser/lean.js').Lean[] }} */ (rhsColon).args.slice()
                    );
                    if (imply[0] instanceof LeanLineComment && imply[0].text === 'imply') imply.shift();

                    const proof0 = assignment.rhs;
                    const by =
                        proof0 instanceof LeanBy
                            ? 'by'
                            : nameOf(proof0) === 'LeanCalc'
                              ? 'calc'
                              : '';
                    const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));

                    let implyLatex;
                    if (imply.length > 1 && nameOf(imply[0]) === 'Lean_let') {
                        implyLatex =
                            '\\begin{align}\n' +
                            imply
                                .map((st) => `&${st.toLatex(syntax)}&& `)
                                .join('\\\\\n') +
                            '\n\\end{align}';
                    } else {
                        implyLatex = imply.map((st) => st.toLatex(syntax)).join('\n');
                    }
                    const assignSuffix = ' :=' + (by ? ` ${by}` : '');
                    implyLatex += `\\tag*{${assignSuffix}}`;
                    const implyOut = { lean: implyLean + assignSuffix, latex: implyLatex };

                    declspec = declspec.lhs;
                    /** @type {string[] | null} */
                    let collectedExplicit = null;
                    /** @type {import('../../../static/js/parser/lean.js').Lean} */
                    let name;
                    if (declspec instanceof LeanToken || declspec instanceof LeanProperty) {
                        name = declspec;
                        declspec = /** @type {*} */ ([]);
                    } else if (
                        declspec &&
                        declspec.args &&
                        declspec.args.length >= 2 &&
                        !(declspec.args[0] && nameOf(declspec.args[0]) === 'LeanParenthesis')
                    ) {
                        /** PHP [name, binders]; skip when args are binders (LeanParenthesis) not name+binders. */
                        const dargs = declspec.args;
                        name = dargs[0];
                        const binders = dargs[1] && dargs[1].args ? dargs[1].args : (dargs.length > 2 ? dargs.slice(1) : []);
                        declspec = binders;
                    } else if (declspec && (declspec.lhs != null || declspec.args)) {
                        /** Parser may produce LeanArgsIndented/LeanArgsSpaceSeparated for (A:T)(V:T). Extract LeanParenthesis nodes. */
                        const collectParens = (/** @type {*} */ n) => {
                            if (!n) return [];
                            if (nameOf(n) === 'LeanParenthesis') return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(declspec);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = /** @type {*} */ (p).arg;
                                if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) lines[lines.length - 1] += ' :';
                            collectedExplicit = lines;
                        }
                        name = stmt.assignment;
                        declspec = /** @type {*} */ ([]);
                    } else {
                        name = stmt.assignment;
                        declspec = /** @type {*} */ ([]);
                    }

                    /** @type {string[]} */
                    const instImplicit = [];
                    /** @type {unknown[]} */
                    const implicit = [];
                    /** @type {string[]} */
                    let explicit = [];
                    /** @type {number | null} */
                    let given = null;
                    /** @type {string[]} */
                    let default_ = [];
                    /** @type {string[]} */
                    const decidables = [];

                    const declList = declspec;
                    for (let i = 0; i < declList.length; ++i) {
                        const st = declList[i];
                        if (nameOf(st) === 'LeanBracket') {
                            instImplicit.push(strStmt(st));
                            const ia = /** @type {*} */ (st).arg;
                            if (ia instanceof LeanArgsSpaceSeparated && ia.args.length === 2) {
                                const [l, r] = ia.args;
                                if (l instanceof LeanToken && l.text === 'Decidable' && r instanceof LeanToken)
                                    decidables.push(strStmt(r));
                            }
                        } else if (nameOf(st) === 'LeanBrace') {
                            st.toLatex(syntax);
                            implicit.push(st);
                        } else if (st instanceof LeanArgsSpaceSeparated) {
                            if (nameOf(st.args[0]) === 'LeanBracket') instImplicit.push(strStmt(st));
                            else if (nameOf(st.args[0]) === 'LeanBrace') implicit.push(st);
                            else
                                error.push({
                                    code: strStmt(st),
                                    line: 0,
                                    info: `lemma ${strStmt(name)} is not well-defined`,
                                    type: 'linter',
                                });
                        } else if (st instanceof LeanLineComment) {
                            if (st.text === 'given') {
                                given = i + 1;
                                break;
                            }
                            if (implicit.length) implicit.push(strStmt(st));
                            else instImplicit.push(strStmt(st));
                        } else if (st instanceof LeanParenthesis) {
                            const inner = /** @type {*} */ (st).arg;
                            if (inner instanceof LeanColon) {
                                declList.splice(
                                    i,
                                    0,
                                    new LeanLineComment('given', st.indent, /** @type {*} */ (st).parent),
                                );
                                if (modify) modify.value = true;
                                ++i;
                            }
                            given = i;
                            break;
                        }
                    }

                    /** @type {unknown} */
                    let givenOut = null;
                    if (given !== null) {
                        let givenSlice = declList.slice(/** @type {number} */ (given));
                        /** @type {([string, string] | null)[]} */
                        const latex = [];
                        let givenStart = null;
                        let givenStop = null;
                        /** @type {Record<string, unknown> | null} */
                        let vars = null;

                        for (const [i, st] of givenSlice.entries()) {
                            if (st instanceof LeanParenthesis) {
                                const colon = /** @type {*} */ (st).arg;
                                if (colon instanceof LeanColon) {
                                    const prop = colon.rhs;
                                    if (vars == null) {
                                        vars = parseVars(implicit);
                                        for (const p of decidables) vars[p] = 'Prop';
                                    }
                                    if (prop.isProp(vars)) {
                                        latex.push([prop.toLatex(syntax), latexTag(strStmt(colon.lhs))]);
                                        if (givenStart === null) givenStart = i;
                                    } else if (givenStart !== null) {
                                        givenStop = i;
                                        break;
                                    }
                                } else if (nameOf(colon) === 'LeanAssign') {
                                    break;
                                }
                            } else if (st.is_comment()) latex.push(null);
                            else if (nameOf(st) === 'LeanBrace') {
                                const pivot = i;
                                const par = new LeanParenthesis(/** @type {*} */ (st).arg, st.indent, st.parent);
                                par.is_closed = true;
                                givenSlice[pivot] = par;
                                break;
                            } else if (st instanceof LeanCaret) {
                                // skip
                            } else {
                                error.push({
                                    code: strStmt(st),
                                    line: 0,
                                    info: 'given statement must be of LeanParenthesis Type',
                                    type: 'linter',
                                });
                            }
                        }

                        givenSlice = givenSlice.map((s) => unindentTwo(strStmt(s)));
                        if (givenStart !== null) {
                            if (givenStop != null) {
                                explicit = givenSlice.slice(0, givenStart);
                                default_ = givenSlice.slice(givenStop);
                                if (default_.length)
                                    default_[default_.length - 1] += ' :';
                                givenSlice = givenSlice.slice(givenStart, givenStop);
                            } else {
                                explicit = givenSlice.slice(0, givenStart);
                                givenSlice = givenSlice.slice(givenStart);
                                const L = latex;
                                if (L.length) {
                                    const lastPair = L[L.length - 1];
                                    if (lastPair) lastPair[1] += ' :';
                                }
                                if (givenSlice.length)
                                    givenSlice[givenSlice.length - 1] += ' :';
                            }
                        } else {
                            explicit = givenSlice;
                            if (explicit.length) explicit[explicit.length - 1] += ' :';
                            givenSlice = [];
                        }

                        if (givenSlice.length) {
                            if (givenSlice.length > latex.length) givenSlice = givenSlice.filter(Boolean);
                            const tagged = latex.map((pair) =>
                                pair
                                    ? `${pair[0]}\\tag*{\\$${pair[1]}$}`
                                    : null,
                            );
                            givenOut = zipped(givenSlice, tagged).map(([g, lx]) => {
                                const o = { lean: g };
                                if (lx) o.latex = lx;
                                else o.insert = true;
                                return o;
                            });
                        }
                    }

                    const proof = assignment.rhs;
                    /** @type {unknown} */
                    let proofOut;
                    /** When rhs is LeanCaret, proof statements live as siblings after the assignment. */
                    let proofNode = proof;
                    if (
                        assignIdx >= 0 &&
                        !(proof instanceof LeanBy || nameOf(proof) === 'LeanCalc') &&
                        (proof instanceof LeanCaret || !(proof?.args && proof.args.length))
                    ) {
                        let end = assignIdx + 1;
                        for (; end < args.length; ++end) {
                            const x = args[end];
                            if (x instanceof LeanLineComment && /^(created|updated)\s/i.test(String(/** @type {*} */ (x).text || '')))
                                break;
                        }
                        proofNode = { args: args.slice(assignIdx + 1, end) };
                    }
                    syntax.letBindings = buildLetBindings(imply?.length ? imply : flatImplyStmts);
                    if (by) {
                        proofOut = { [by]: mergeProof(proofNode?.arg ?? proofNode, echo, syntax) };
                    } else {
                        proofOut = mergeProof(proofNode, echo, syntax);
                    }

                    const implicitStr = unindentTwo(
                        implicit.map((x) => (typeof x === 'string' ? x : strStmt(x))).join('\n'),
                    );

                    lemma.push({
                        comment,
                        accessibility: String(accessibility),
                        attribute,
                        name: strStmt(name).trim(),
                        instImplicit: normalizeInstImplicit(
                            unindentTwo(
                                instImplicit.length ? instImplicit.join('\n') : flatInstImplicit.join('\n'),
                            ),
                        ),
                        implicit: implicitStr,
                        explicit: collectedExplicit ? collectedExplicit.join('\n') : (explicit.length ? explicit.join('\n') : flatExplicit),
                        given: givenOut ?? flatGiven,
                        default: default_.join('\n'),
                        imply: implyOut,
                        proof: proofOut,
                    });
                    comment = null;
                } else if (declspec && (typeof declspec.toLatex === 'function' || flatImplyStmts?.length > 0)) {
                    const proof0 = assignment.rhs;
                    const by =
                        proof0 instanceof LeanBy
                            ? 'by'
                            : nameOf(proof0) === 'LeanCalc'
                              ? 'calc'
                              : '';
                    /** When declspec is LeanColon, extract explicit (A:T)(V:T) from lhs and imply from rhs. */
                    let simpleExplicit = flatExplicit;
                    let implyNode = declspec;
                    if (declspec instanceof LeanColon && declspec.lhs && !flatExplicit) {
                        const inner = declspec.lhs;
                        /** Binders may be in inner (LeanColon), inner.lhs (LeanArgsIndented), or inner.lhs.lhs. */
                        const binderNode =
                            inner.lhs instanceof LeanColon
                                ? inner.lhs.lhs
                                : inner;
                        const collectParens = (/** @type {import('../../../static/js/parser/lean.js').Lean} */ n) => {
                            if (!n) return [];
                            if (nameOf(n) === 'LeanParenthesis') return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(binderNode);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = /** @type {*} */ (p).arg;
                                if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) {
                                lines[lines.length - 1] += ' :';
                                simpleExplicit = lines.join('\n');
                            }
                        }
                        /** Imply = LeanStatements from inner.rhs, or inner.lhs.rhs when triple-nested. */
                        const innerLhs = inner.lhs;
                        implyNode =
                            (innerLhs && innerLhs.rhs && (nameOf(innerLhs.rhs) === 'LeanStatements' || nameOf(innerLhs.rhs) === 'LeanArgsNewLineSeparated'))
                                ? innerLhs.rhs
                                : inner.rhs || declspec;
                    }
                    let implyOut;
                    if (flatImplyStmts && flatImplyStmts.length > 0) {
                        const imply = [...flatImplyStmts, assignment.lhs];
                        const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                        let implyLatex;
                        if (imply.length > 1 && (nameOf(imply[0]) === 'Lean_let' || nameOf(imply[0]) === 'Lean_have')) {
                            implyLatex =
                                '\\begin{align}\n' +
                                imply
                                    .map((st) => `&${st.toLatex ? st.toLatex(syntax) : strStmt(st)}&& `)
                                    .join('\\\\\n') +
                                '\n\\end{align}';
                        } else {
                            implyLatex = imply
                                .map((st) => (st.toLatex ? st.toLatex(syntax) : strStmt(st)))
                                .join('\n');
                        }
                        implyLatex += `\\tag*{ :=${by ? ` ${by}` : ''}}`;
                        implyOut = { lean: implyLean + ' :=' + (by ? ` ${by}` : ''), latex: implyLatex };
                    } else {
                        const implyLean = unindentTwo(strStmt(implyNode)) + ' :=' + (by ? ` ${by}` : '');
                        const implyLatex =
                            (implyNode.toLatex ? implyNode.toLatex(syntax) : strStmt(implyNode)) +
                            `\\tag*{ :=${by ? ` ${by}` : ''}}`;
                        implyOut = { lean: implyLean, latex: implyLatex };
                    }
                    syntax.letBindings = buildLetBindings(flatImplyStmts ?? []);
                    const proof = assignment.rhs;
                    let proofOut;
                    const proofArg = proof && typeof proof === 'object' && 'arg' in proof ? proof.arg : proof;
                    const hasProofArgs = proofArg && typeof proofArg === 'object' && Array.isArray(proofArg.args);
                    if (by) {
                        proofOut = { [by]: hasProofArgs ? mergeProof(proofArg, echo, syntax) : [] };
                    } else {
                        proofOut = hasProofArgs ? mergeProof(proofArg, echo, syntax) : [{ lean: strStmt(proof || ''), latex: null }];
                    }
                    let attribute = extractAttribute(stmt.attribute);
                    const name = stmt.assignment;
                    lemma.push({
                        comment,
                        accessibility: String(stmt.accessibility),
                        attribute,
                        name: strStmt(name).trim(),
                        instImplicit: normalizeInstImplicit(unindentTwo(flatInstImplicit.join('\n'))),
                        implicit: '',
                        explicit: simpleExplicit,
                        given: flatGiven,
                        default: '',
                        imply: implyOut,
                        proof: proofOut,
                    });
                    comment = null;
                } else {
                    error.push({
                        code: strStmt(declspec),
                        line: 0,
                        info: 'declspec of lemma must be of LeanColon Type',
                        type: 'linter',
                    });
                }
            } else {
                error.push({
                    code: strStmt(stmt),
                    line: 0,
                    info: 'lemma must be of LeanAssign Type',
                    type: 'linter',
                });
            }
        } else if (stmt instanceof Lean_def) {
            def.push(strStmt(stmt));
        } else if (nameOf(stmt) === 'Lean_open') {
            let o = /** @type {*} */ (stmt).arg;
            if (o instanceof LeanArgsSpaceSeparated) {
                if (o.args.length === 2 && o.args[1] instanceof LeanParenthesis) {
                    const defs = /** @type {*} */ (o.args[1]).arg;
                    open.push({
                        [strStmt(o.args[0])]:
                            defs instanceof LeanArgsSpaceSeparated
                                ? defs.args.map((a) => strStmt(a))
                                : [strStmt(/** @type {*} */ (defs).arg)],
                    });
                } else open.push(o.args.map((a) => strStmt(a)).filter((s) => s.trim()));
            } else open.push([strStmt(/** @type {*} */ (o).text)]);
        } else if (nameOf(stmt) === 'Lean_set_option') {
            const a = /** @type {*} */ (stmt).arg;
            if (a instanceof LeanArgsSpaceSeparated) set_option.push(a.args.map((x) => strStmt(x)));
        } else if (stmt instanceof LeanLineComment) {
            const m = /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.exec(stmt.text);
            if (m) date[m[1]] = m[2];
            else comment = stmt.text;
        } else if (nameOf(stmt) === 'LeanBlockComment') {
            comment = /** @type {*} */ (stmt).text;
        }
    }

    return {
        imports: import_,
        open,
        set_option,
        def,
        lemma,
        date,
        error,
    };
}

/**
 * @param {string} source
 * @param {boolean} [echo]
 */
export function render2vueFromSource(source, echo = false) {
    const tree = compile(source);
    if (!(tree instanceof LeanModule)) throw new Error('compile() root must be LeanModule');
    const modify = { value: false };
    const syntax = {};
    return render2vue(tree, echo, modify, syntax);
}
