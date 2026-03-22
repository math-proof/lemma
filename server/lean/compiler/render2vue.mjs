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

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function nameOf(node) {
    return node && node.constructor && node.constructor.name;
}

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function strStmt(node) {
    return String(node).replace(/\n$/, '');
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
 * Port of `LeanModule::merge_proof` (php/parser/lean.php ~4685–4725).
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

    return code.map(([stmts, latex]) => ({
        lean: unindentTwo(stmts.map((st) => strStmt(st)).join('\n')),
        latex,
    }));
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
            import_.push(strStmt(/** @type {*} */ (stmt).arg));
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
                if (assignIdx >= 0) {
                    let firstAssign = assignIdx;
                    for (let k = idx + 1; k < assignIdx; k++) {
                        if (args[k] instanceof LeanAssign) {
                            firstAssign = k;
                            break;
                        }
                    }
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
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
                        if (assignIdx >= 0 && assignment.lhs && typeof assignment.lhs.toLatex === 'function') {
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
                    let attribute = stmt.attribute;
                    if (attribute) {
                        attribute = /** @type {*} */ (attribute).arg;
                        if (nameOf(attribute) === 'LeanBracket') {
                            attribute = /** @type {*} */ (attribute).arg;
                            if (attribute instanceof LeanArgsSpaceSeparated)
                                attribute = attribute.args.map((a) => strStmt(a));
                            else if (attribute instanceof LeanToken) attribute = [strStmt(attribute)];
                        }
                    }
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
                    /** @type {import('../../../static/js/parser/lean.js').Lean} */
                    let name;
                    if (declspec instanceof LeanToken || declspec instanceof LeanProperty) {
                        name = declspec;
                        declspec = /** @type {*} */ ([]);
                    } else if (declspec && declspec.args && declspec.args.length >= 2) {
                        const dargs = declspec.args;
                        name = dargs[0];
                        declspec = dargs[1] && dargs[1].args ? dargs[1].args : [];
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
                    if (by) {
                        proofOut = { [by]: mergeProof(/** @type {*} */ (proof).arg, echo, syntax) };
                    } else {
                        proofOut = mergeProof(proof, echo, syntax);
                    }

                    const implicitStr = unindentTwo(
                        implicit.map((x) => (typeof x === 'string' ? x : strStmt(x))).join('\n'),
                    );

                    lemma.push({
                        comment,
                        accessibility: String(accessibility),
                        attribute,
                        name: strStmt(name),
                        instImplicit: unindentTwo(
                            instImplicit.length ? instImplicit.join('\n') : flatInstImplicit.join('\n'),
                        ),
                        implicit: implicitStr,
                        explicit: explicit.length ? explicit.join('\n') : flatExplicit,
                        given: givenOut ?? flatGiven,
                        default: default_.join('\n'),
                        imply: implyOut,
                        proof: proofOut,
                    });
                    comment = null;
                } else if (declspec && typeof declspec.toLatex === 'function') {
                    const imply = [declspec];
                    const proof0 = assignment.rhs;
                    const by =
                        proof0 instanceof LeanBy
                            ? 'by'
                            : nameOf(proof0) === 'LeanCalc'
                              ? 'calc'
                              : '';
                    const implyLean = unindentTwo(strStmt(declspec)) + ' :=' + (by ? ` ${by}` : '');
                    const implyLatex =
                        (declspec.toLatex ? declspec.toLatex(syntax) : strStmt(declspec)) +
                        `\\tag*{ :=${by ? ` ${by}` : ''}}`;
                    const implyOut = { lean: implyLean, latex: implyLatex };
                    const proof = assignment.rhs;
                    let proofOut;
                    const proofArg = proof && typeof proof === 'object' && 'arg' in proof ? proof.arg : proof;
                    const hasProofArgs = proofArg && typeof proofArg === 'object' && Array.isArray(proofArg.args);
                    if (by) {
                        proofOut = { [by]: hasProofArgs ? mergeProof(proofArg, echo, syntax) : [] };
                    } else {
                        proofOut = hasProofArgs ? mergeProof(proofArg, echo, syntax) : [{ lean: strStmt(proof || ''), latex: null }];
                    }
                    let attribute = stmt.attribute;
                    if (attribute) {
                        attribute = /** @type {*} */ (attribute).arg;
                        if (nameOf(attribute) === 'LeanBracket') {
                            attribute = /** @type {*} */ (attribute).arg;
                            if (attribute instanceof LeanArgsSpaceSeparated)
                                attribute = attribute.args.map((a) => strStmt(a));
                            else if (attribute instanceof LeanToken) attribute = [strStmt(attribute)];
                        }
                    } else attribute = null;
                    const name = stmt.assignment;
                    lemma.push({
                        comment,
                        accessibility: String(stmt.accessibility),
                        attribute,
                        name: strStmt(name),
                        instImplicit: unindentTwo(flatInstImplicit.join('\n')),
                        implicit: '',
                        explicit: flatExplicit,
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
                } else open.push(o.args.map((a) => strStmt(a)));
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
