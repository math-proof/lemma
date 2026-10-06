/**
 * Source file (`LeanModule`).
 *
 * Imply LaTeX, echo-proof tails, and `render2vue` live here with the class.
 * `strStmt` lives in `utility.js` because `base`, `args`, and `bigops` use it too.
 * PHP `echo2vue` chdirs four directories up, because `module.php` lives in `lean/`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { strStmt } from './utility.js';
import { LeanStatements } from './statements.js';
import { Lean } from './base.js';

const L = Lean.classes;

/**
 * Conjuncts of a `∧` chain whose source breaks a line after some `∧`, else null.
 * @param {unknown} node
 */
function landMultilineConjuncts(node) {
    if (!(node instanceof L.Lean_land)) return null;
    const out = [];
    let multiline = false;
    const walk = (n) => {
        if (n instanceof L.Lean_land) {
            if (n.hanging_indentation) multiline = true;
            walk(n.lhs);
            walk(n.rhs);
        } else out.push(n instanceof L.LeanParenthesis ? n.arg : n); // own line: parentheses are redundant
    };
    walk(node);
    return multiline && out.length > 1 ? out : null;
}

/**
 * LaTeX for an `imply` conclusion: a `∧` chain written on several lines renders one conjunct per line.
 * @param {any} node
 * @param {any} syntax
 */
function implyConclusionLatex(node, syntax) {
    const parts = landMultilineConjuncts(node);
    if (!parts) return node.toLatex ? node.toLatex(syntax) : strStmt(node);
    const rows = parts.map(
        (c, i) => `&${c.toLatex ? c.toLatex(syntax) : strStmt(c)}${i < parts.length - 1 ? ' \\land' : ''}`,
    );
    return '\\begin{align*}\n' + rows.join('\\\\\n') + '\n\\end{align*}';
}

/**
 * `align*` for imply statements that start with `have`/`let`: one row per statement, and a
 * `∧` chain written on several lines contributes one row per conjunct.
 * @param {any[]} imply
 * @param {any} syntax
 */
function implyLetAlignLatex(imply, syntax) {
    const tex = (n) => (n.toLatex ? n.toLatex(syntax) : strStmt(n));
    const rows = [];
    for (const st of imply) {
        const parts = landMultilineConjuncts(st);
        if (parts) parts.forEach((c, i) => rows.push(`&${tex(c)}${i < parts.length - 1 ? ' \\land' : ''}&& `));
        else rows.push(`&${tex(st)}&& `);
    }
    return '\\begin{align*}\n' + rows.join('\\\\\n') + '\n\\end{align*}';
}

/**
 * Echo-style `:= by` proofs: `LeanTactic` may indent continuation lines (nested tactics under
 * `intro`); `LeanModule` then applies `indentText(proofInd)` to the whole string, doubling those
 * spaces and changing how the next parse groups tactics. Remove the common leading whitespace
 * from lines after the first so outer indent is applied once.
 * @param {string} s
 */
function dedentEchoProofTacticLines(s) {
    const lines = s.split('\n');
    if (lines.length < 2) return s;
    let minLead = Infinity;
    for (let i = 1; i < lines.length; i++) {
        const line = lines[i];
        if (line === '') continue;
        const lead = /^ */.exec(line);
        if (lead) minLead = Math.min(minLead, lead[0].length);
    }
    if (!Number.isFinite(minLead) || minLead === 0) return s;
    const out = [lines[0]];
    for (let i = 1; i < lines.length; i++) {
        const line = lines[i];
        if (line === '') out.push(line);
        else out.push(line.slice(minLead));
    }
    return out.join('\n');
}

function dedentEchoProofTermBlock(s) {
    const lines = s.split('\n');
    let minLead = Infinity;
    for (const line of lines) {
        if (line === '') continue;
        const lead = /^ */.exec(line);
        if (lead) minLead = Math.min(minLead, lead[0].length);
    }
    if (!Number.isFinite(minLead) || minLead === 0) return s;
    return lines.map((line) => (line === '' ? line : line.slice(minLead))).join('\n');
}

/**
 * Scan module args after `LeanAssign`/`Lean_def` with empty rhs caret: optional carets, line comments,
 * then `LeanTactic`, space-separated term, a single `LeanToken`, or `Lean_fun` proof. Used for echo `:= by` serialization.
 * @param {Lean[]} moduleArgs
 * @param {number} startJ
 * @param {(s: string, indent: number) => string} indentText
 * @returns {{ cmts: Lean[], proofStr: string, endJ: number, proofIsTactic: boolean } | null}
 */
function consumeEchoAssignProofTail(moduleArgs, startJ, indentText) {
    let j = startJ;
    while (j < moduleArgs.length && moduleArgs[j] instanceof L.LeanCaret) j++;
    const cmts = [];
    while (j < moduleArgs.length && moduleArgs[j].is_comment()) {
        cmts.push(moduleArgs[j]);
        j++;
    }
    const proof = j < moduleArgs.length ? moduleArgs[j] : null;
    const proofOk =
        proof &&
        (proof instanceof L.LeanTactic ||
            proof instanceof L.LeanArgsSpaceSeparated ||
            proof instanceof L.LeanToken ||
            proof instanceof L.Lean_fun ||
            proof instanceof L.LeanAngleBracket);
    if (!proofOk) return null;
    let endJ = j;
    let proofStr = String(proof);
    let proofInd = proof.indent ?? 0;
    for (const c of cmts) proofInd = Math.max(proofInd, c.indent ?? 0);
    const proofIsTactic = proof instanceof L.LeanTactic;
    if (proofIsTactic) {
        const tacticProofRaw = dedentEchoProofTacticLines(String(proof));
        let danglingStc = false;
        for (let k = 0; k < proof.args.length; k++) {
            const x = proof.args[k];
            if (x instanceof L.LeanSequentialTacticCombinator && x.arg instanceof L.LeanCaret) {
                danglingStc = true;
                break;
            }
        }
        if (danglingStc && endJ + 1 < moduleArgs.length && moduleArgs[endJ + 1] instanceof L.LeanTacticBlock) {
            endJ++;
            const ps = indentText(tacticProofRaw, proofInd);
            const tb = String(moduleArgs[endJ]);
            const join = ps.endsWith('\n') ? '' : '\n';
            proofStr = `${ps}${join}${tb}`;
        } else {
            proofStr = indentText(tacticProofRaw, proofInd);
        }
    } else {
        proofStr = indentText(dedentEchoProofTermBlock(String(proof)), proofInd);
    }
    return { cmts, proofStr, endJ, proofIsTactic };
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
 * Extract attribute names from LeanAttribute (e.g. @[main] → ['main'], @[main, fin] → ['main','fin']).
 * Handles LeanBracket contents as LeanArgsCommaSeparated, LeanArgsSpaceSeparated, or LeanToken.
 */
function extractAttribute(attr) {
    if (!attr) return null;
    let a = attr.arg;
    if (a instanceof L.LeanArgsSpaceSeparated) {
        const bracket = a.args.find((x) => x instanceof L.LeanBracket);
        a = bracket || null;
    }
    if (!a || !(a instanceof L.LeanBracket)) return null;
    a = a.arg;
    if (a instanceof L.LeanArgsCommaSeparated || a instanceof L.LeanArgsSpaceSeparated)
        return a.args.map((x) => strStmt(x)).filter(Boolean);
    if (a instanceof L.LeanToken) return [strStmt(a)];
    return null;
}

/**
 * `(hS : StochasticIrreducible P)` / `(h₁ : Measurable Y)` — a hypothesis-named binder whose
 * type is a predicate application (capitalized head, not a known type former). `isProp` cannot
 * see the declaration of such predicates, so the naming convention decides.
 * @param {Lean} name
 * @param {Lean} type
 */
function looksLikeClassHypothesis(name, type) {
    if (!(name instanceof L.LeanToken)) return false;
    let head = type instanceof L.LeanArgsSpaceSeparated ? type.args[0] : type;
    if (head instanceof L.LeanProperty && head.rhs instanceof L.LeanToken) head = head.rhs;
    if (!(head instanceof L.LeanToken) || !/^[A-Z]/.test(head.text)) return false;
    // Well-known Prop-valued predicates: a hypothesis whatever the binder is called
    // (`(mono : Monotone t)`, `(f_mono : Monotone f)`).
    if (/^(Monotone|Antitone|StrictMono|StrictAnti|MonotoneOn|AntitoneOn|StrictMonoOn|StrictAntiOn|Summable|HasSum|Continuous|ContinuousOn|ContinuousAt|Differentiable|DifferentiableOn|DifferentiableAt|HasDerivAt|Integrable|IntegrableOn|Measurable|AEMeasurable|StronglyMeasurable|AEStronglyMeasurable|Injective|Surjective|Bijective|Tendsto|Nonempty|Convex|ConvexOn|ConcaveOn|IsCompact|IsOpen|IsClosed|Pairwise|Irreducible|Prime|Even|Odd|Squarefree|Coprime|IsUnit)$/.test(head.text))
        return true;
    // Otherwise rely on the naming convention: `h`, `h₁`, `hf`, `hmono`, `hμ`, …
    if (!/^h/u.test(name.text)) return false;
    return !/^(Type|Sort|Prop|Fin|Set|Finset|Multiset|List|Array|Vector|Matrix|Tensor|Measure|MeasurableSpace|Option|Nat|Int|Real|Complex|Bool|String|Prod|Sum|Sigma|Subtype|Filter|EuclideanSpace|PMF|ProbabilityMeasure|FiniteMeasure)$/.test(head.text);
}

/**
 * `(f : S → α)`: a function-valued data argument (codomain is a type), not a hypothesis.
 * `Lean_rightarrow.isProp` defaults undeclared tokens to `Prop`, which misfiles such binders
 * as givens while `(n : ℕ)` stays explicit.
 * @param {Lean} type
 * @param {Record<string, unknown>} vars
 * @param {Set<string>} typeVars
 */
function looksLikeDataArrow(type, vars, typeVars) {
    if (!(type instanceof L.Lean_rightarrow)) return false;
    let cod = type;
    while (cod instanceof L.Lean_rightarrow) cod = cod.rhs;
    if (!(cod instanceof L.LeanToken)) return false;
    const t = cod.text;
    if (vars[t] === 'Prop') return false;
    return typeVars.has(t) ||
        /^(ℕ|ℤ|ℚ|ℝ|ℂ|Bool|Prop|Type|Nat|Int|Rat|Real|Complex|ENNReal|NNReal|EReal|ℝ≥0|ℝ≥0∞)$/u.test(t);
}

/**
 * PHP `escape_specials` (php/parser/lean.php ~9331–9341).
 * @param {string} token
 */
function escapeSpecials(token) {
    return token.replace(/^(_*)([^\W_]\w*?)_(.+)/, (_m, lead, head, tail) => {
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        const escLead = lead.replace(/_/g, '\\_');
        return !lead && head.length === 1 ? `${head}_{${escTail}}` : `${escLead}${head}\\_${escTail}`;
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
 * @param {import('../lean.js').Lean} lhs
 * @param {import('../lean.js').Lean} rhs
 */
function arrayPushVars(vars, lhs, rhs) {
    if (lhs instanceof L.LeanToken) {
        /** @type {import('../lean.js').Lean[]} */
        let args = [lhs, rhs];
        while (args.length && args[args.length - 1] instanceof L.Lean_rightarrow) {
            const end = args[args.length - 1];
            args.splice(args.length - 1, 1, end.lhs, end.rhs);
        }
        vars.push(args);
    } else if (lhs instanceof L.LeanArgsSpaceSeparated) {
        for (const sub of lhs.args) arrayPushVars(vars, sub, rhs);
    }
}

/**
 * @param {unknown[]} implicit
 */
function parseVars(implicit) {
    const vars = [];
    // `{S : Type*} [Fintype S]` on one line arrives as a single space-separated node
    const flat = [];
    for (const b of implicit) {
        if (b instanceof L.LeanArgsSpaceSeparated) flat.push(...b.args);
        else flat.push(b);
    }
    for (const brace of flat) {
        if (brace instanceof L.LeanBrace) {
            const colon = brace.arg;
            if (colon instanceof L.LeanColon) arrayPushVars(vars, colon.lhs, colon.rhs);
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

function collectRandomVarNames(binderRoots) {
    const nodes = [];
    const gather = (n) => {
        if (!n || typeof n !== 'object') return;
        nodes.push(n);
        if (Array.isArray(n.args)) for (const k of n.args) gather(k);
    };
    for (const r of binderRoots) gather(r);

    /** @type {Map<string, string>} measure name -> domain text */
    const measures = new Map();
    for (const n of nodes) {
        if (!(n instanceof L.LeanBrace)) continue;
        const cols = [];
        const a = n.arg;
        if (a instanceof L.LeanColon) cols.push(a);
        else if (a instanceof L.LeanArgsSpaceSeparated)
            for (const c of a.args) if (c instanceof L.LeanColon) cols.push(c);
        for (const col of cols) {
            const rhs = col.rhs.peelGroup();
            if (rhs.headIs('Measure') && rhs instanceof L.LeanArgsSpaceSeparated
                && rhs.args.length >= 2) {
                const dom = strStmt(rhs.args[1].peelGroup()).trim();
                if (dom) measures.set(strStmt(col.lhs).trim(), dom);
            }
        }
    }
    const probMeasureApp = (n0) => {
        const a = n0?.peelGroup?.() ?? n0;
        if (!(a instanceof L.LeanArgsSpaceSeparated) || a.args.length < 2) return null;
        if (!a.headIs('IsProbabilityMeasure') && !a.headIs('PSpace')) return null;
        return a.args[1];
    };

    const probDomains = new Set();
    const addProbMeasure = (measureName) => {
        if (measureName == null) return;
        const m = strStmt(measureName.peelGroup()).trim();
        if (measures.has(m)) probDomains.add(measures.get(m));
    };
    for (const n of nodes) {
        if (n instanceof L.LeanBracket) {
            addProbMeasure(probMeasureApp(n.arg));
        } else if (n instanceof L.LeanParenthesis && n.arg instanceof L.LeanColon) {
            addProbMeasure(probMeasureApp(n.arg.rhs));
        }
    }

    /** @type {Set<string>} */
    const rvs = new Set();
    for (const n of nodes) {
        if (!(n instanceof L.LeanParenthesis) && !(n instanceof L.LeanBrace)) continue;
        const cols = [];
        const a = n.arg;
        if (a instanceof L.LeanColon) cols.push(a);
        else if (a instanceof L.LeanArgsSpaceSeparated)
            for (const c of a.args) if (c instanceof L.LeanColon) cols.push(c);
        for (const col of cols) {
            const ty = col.rhs.peelGroup();
            if (!(ty instanceof L.Lean_rightarrow)) continue;
            // `X : Ω → S`, or an indexed family `s : ℕ → Ω → S` (the last domain is Ω)
            let last = ty;
            while (last.rhs.peelGroup() instanceof L.Lean_rightarrow) last = last.rhs.peelGroup();
            const dom = strStmt(ty.lhs.peelGroup()).trim();
            if (!probDomains.has(dom) && !probDomains.has(strStmt(last.lhs.peelGroup()).trim())) continue;
            const addNames = (x) => {
                const y = x.peelGroup();
                if (y instanceof L.LeanToken) rvs.add(y.text);
                else if (y instanceof L.LeanArgsSpaceSeparated) y.args.forEach(addNames);
            };
            addNames(col.lhs);
        }
    }
    return rvs;
}

/**
 * Mark a sequence of statements in order: a top-level `let q := …` hides `q`
 * for every following statement (the shared `letBound` frame accumulates).
 * @param {unknown[]} stmts
 * @param {Set<string>} rvNames
 */
function markRandomVarSequence(stmts, rvNames) {
    const letBound = [];
    for (const st of stmts) st.markRandomVarNames(rvNames, letBound);
}

function zipped(a, b) {
    const n = Math.min(a.length, b.length);
    /** @type {[T, U][]} */
    const out = [];
    for (let i = 0; i < n; ++i) out.push([a[i], b[i]]);
    return out;
}

function buildLetBindings(implyStmts) {
    const bindings = {};
    if (!implyStmts.length) return bindings;
    for (const stmt of implyStmts) {
        if (!(stmt instanceof L.Lean_let)) continue;
        const arg = stmt.arg;
        if (!arg) continue;
        let nameNode = null;
        let rhsNode = null;
        if (arg instanceof L.LeanAssign) {
            if (arg.lhs instanceof L.LeanColon) {
                nameNode = arg.lhs.lhs;
                rhsNode = arg.rhs;
            } else {
                nameNode = arg.lhs;
                rhsNode = arg.rhs;
            }
        } else if (arg instanceof L.LeanColon && arg.rhs instanceof L.LeanAssign) {
            nameNode = arg.rhs.lhs;
            rhsNode = arg.rhs.rhs;
        }
        if (nameNode && rhsNode) {
            const name = strStmt(nameNode).trim();
            if (name) bindings[name] = rhsNode;
        }
    }
    return bindings;
}

function leanModuleMergeProof(proof, echo, syntax = {}) {
    let list = proof.args;
    if (list[0] instanceof L.LeanLineComment && list[0].text === 'proof') list = list.slice(1);
    list = list.filter((s) => !(s instanceof L.LeanCaret));

    const statements = [];
    for (const s of list) statements.push(...s.split(syntax));

    const code = [];
    let last = [];
    // Separator inserted BEFORE each statement in `last` (' ' for the rhs of a
    // same-line `<;>` chain, '\n' otherwise).
    let seps = [];
    let nextSep = '\n';
    // Goal LaTeX captured by an inline `<;> echo ⊢` marker for the open step.
    let inlineLatex;

    const echoLatex = (echoNode) => {
        const {line} = echoNode;
        return Number.isInteger(line) ? null : line == null ? null : line;
    };
    // A same-line `<;> echo ⊢` combinator (newlineBehind === false) is a goal
    // snapshot INSIDE one source line, e.g. `split_ifs <;> echo ⊢ <;> first | …`:
    // it must not become its own step nor print its marker text. The surrounding
    // chain is glued onto one step and the snapshot is attached as its LaTeX.
    const isInlineEchoMark = (stmt, echoNode) =>
        !!echoNode
        && stmt instanceof L.LeanSequentialTacticCombinator
        && stmt.newlineBehind === false;

    if (echo) {
        for (const stmt of statements) {
            const echoNode = stmt.getEcho();
            if (isInlineEchoMark(stmt, echoNode)) {
                if (inlineLatex === undefined || inlineLatex === null)
                    inlineLatex = echoLatex(echoNode);
                nextSep = ' ';
            } else if (echoNode) {
                code.push([last, inlineLatex !== undefined ? inlineLatex : echoLatex(echoNode), seps]);
                last = [];
                seps = [];
                nextSep = '\n';
                inlineLatex = undefined;
            } else {
                seps.push(nextSep);
                last.push(stmt);
                nextSep = '\n';
            }
        }
    } else {
        for (const stmt of statements) {
            if (stmt instanceof L.Lean_let || stmt instanceof L.LeanTactic) {
                last.push(stmt);
                code.push([last, null, seps]);
                last = [];
            } else last.push(stmt);
        }
    }
    if (last.length) {
        let finalLatex = inlineLatex !== undefined ? inlineLatex : null;
        if (finalLatex === null && last[0] instanceof L.LeanCalc && last[0].originalCalc)
            finalLatex = last[0].originalCalc.toLatex(syntax);
        code.push([last, finalLatex, seps]);
    }

    return code.map(([stmts, latex, ss]) => {
        let text = '';
        stmts.forEach((st, i) => {
            text += (i === 0 ? '' : (ss && ss[i] ? ss[i] : '\n')) + strStmt(st);
        });
        return {lean: unindentTwo(text), latex};
    });
}

function leanModuleRender2vue(mod, echo, modify = null, syntax = {}) {
    if (!echo) mod.relocate_last_comment();
    const $import = [];
    const open = [];
    const set_option = [];
    const preamble = [];
    const lemma = [];
    const date = {};
    const error = [];
    let comment = null;

    const args = mod.args;
    for (let idx = 0; idx < args.length; idx++) {
        const stmt = args[idx];
        if (stmt instanceof L.Lean_import)
            $import.push(normalizeImportStr(strStmt(stmt.arg)));
        else if (stmt instanceof L.Lean_lemma) {
            let assignment = stmt.assignment instanceof L.LeanAssign ? stmt.assignment : null;

            let assignIdx = -1;
            if (!assignment) {
                let proofStart = args.length;
                for (let k = idx + 1; k < args.length; k++) {
                    const x = args[k];
                    if (x instanceof L.LeanLineComment && x.text === 'proof') {
                        proofStart = k;
                        break;
                    }
                    if (x instanceof L.LeanTactic) {
                        proofStart = k;
                        break;
                    }
                }
                for (let j = idx + 1; j < proofStart; j++) {
                    const cand = args[j];
                    if (cand instanceof L.LeanAssign) {
                        const lhs = cand.lhs;
                        if (lhs instanceof L.Lean_let) continue;
                        assignment = cand;
                        assignIdx = j;
                    }
                }
                if (!assignment) {
                    for (let j = idx + 1; j < args.length; j++) {
                        const cand = args[j];
                        if (cand instanceof L.LeanAssign) {
                            assignment = cand;
                            assignIdx = j;
                            break;
                        }
                    }
                }
            }
            if (assignment instanceof L.LeanAssign) {
                const accessibility = stmt.accessibility;
                let innerAssign = assignment;
                while (innerAssign.lhs instanceof L.LeanAssign) innerAssign = innerAssign.lhs;
                let declspec = innerAssign.lhs;
                while (declspec instanceof L.LeanAssign) declspec = declspec.lhs;
                let flatInstImplicit = [];
                let flatExplicit = '';
                let flatGiven = null;

                let flatImplyStmts = [];
                let flatRvNames = new Set();
                if (assignIdx >= 0) {
                    let firstAssign = assignIdx;
                    for (let k = idx + 1; k < assignIdx; k++) {
                        if (args[k] instanceof L.LeanAssign) {
                            firstAssign = k;
                            break;
                        }
                    }
                    // semantic pass: random-variable names + free-occurrence
                    // marking, before any given/imply latex is generated
                    const flatBinderNodes = args.slice(idx + 1, firstAssign);
                    flatRvNames = collectRandomVarNames(flatBinderNodes);
                    for (const s of flatBinderNodes) s.markRandomVarNames(flatRvNames);
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (s instanceof L.Lean_let) {
                            flatImplyStmts.push(s);
                        }
                    }
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (s instanceof L.LeanBracket) {
                            flatInstImplicit.push(strStmt(s));
                            continue;
                        }
                        const collectParenColons = (/** @type {*} */ n) => {
                            if (!n) return;
                            if (n instanceof L.LeanParenthesis && n.arg instanceof L.LeanColon) {
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
                        if (s instanceof L.LeanParenthesis && s.arg instanceof L.LeanColon) {
                            collectParenColons(s);
                            continue;
                        }
                        if (s instanceof L.LeanArgsSpaceSeparated || s instanceof L.LeanArgsNewLineSeparated) {
                            collectParenColons(s);
                            continue;
                        }
                        if (s instanceof L.LeanColon && s.lhs) {
                            const lb = s.lhs;
                            if (lb instanceof L.LeanBracket) {
                                const inner = lb.arg;
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
                            } else if (lb instanceof L.LeanParenthesis || (lb instanceof L.LeanColon && lb.rhs)) {
                                if (s.rhs instanceof L.LeanStatements || s.rhs instanceof L.LeanArgsNewLineSeparated) {
                                    const inner = lb;
                                    if (inner instanceof L.LeanColon && inner.lhs && inner.rhs) {
                                        const innerLhs = inner.lhs;
                                        if (innerLhs instanceof L.LeanParenthesis && inner.rhs) {
                                            if (flatGiven === null) flatGiven = [];
                                            const varPart = strStmt(
                                                innerLhs.arg
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
                                    if (lb instanceof L.LeanParenthesis && s.rhs) {
                                        const varPart = strStmt(lb.arg).trim();
                                        const typePart = normalizeTypeStr(strStmt(s.rhs));
                                        leanStr = `(${varPart} : ${typePart})`;
                                    } else {
                                        leanStr = strStmt(s).trim();
                                        if (lb instanceof L.LeanParenthesis && !leanStr.startsWith('('))
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
                if (declspec instanceof L.LeanColon) {
                    const rhsColon = declspec.rhs;
                    const rhsArgs = rhsColon.args?? null;
                    const isImplyList =
                        rhsArgs &&
                        Array.isArray(rhsArgs) &&
                        rhsArgs.length > 0 &&
                        (rhsArgs[0] instanceof L.LeanLineComment ||
                            rhsArgs[0] instanceof L.Lean_let ||
                            rhsColon instanceof L.LeanArgsSpaceSeparated ||
                            rhsColon instanceof L.LeanStatements ||
                            rhsColon instanceof L.LeanArgsNewLineSeparated);
                    if (!rhsColon || !rhsArgs || !isImplyList) {
                        if (
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
                if (declspec instanceof L.LeanColon && !useSimpleDeclspec) {
                    const rhsColon = declspec.rhs;
                    let attribute = extractAttribute(stmt.attribute);
                    let imply =  rhsColon.args.slice()
                    if (imply[0] instanceof L.LeanLineComment && imply[0].text === 'imply') imply.shift();
                    // semantic pass: random variables are explicit binders on a
                    // probability-space domain; mark their free occurrences in
                    // the signature propositions and the imply statements
                    const rvNames = collectRandomVarNames([declspec.lhs]);
                    // Always run: `.map` argument detection marks random
                    // variables even when no PSpace hypothesis is present.
                    declspec.lhs.markRandomVarNames(rvNames);
                    markRandomVarSequence(imply, rvNames);
                    const proof0 = innerAssign.rhs;
                    const by = proof0 instanceof L.LeanBy? 'by' : proof0 instanceof L.LeanCalc ? 'calc' : '';
                    const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                    let implyLatex;
                    if (imply.length > 1 && imply[0] instanceof L.Lean_let)
                        implyLatex = implyLetAlignLatex(imply, syntax);
                    else
                        implyLatex = imply.map(st => implyConclusionLatex(st, syntax)).join('\n');
                    const assignSuffix = ' :=' + (by ? ` ${by}` : '');

                    const implyOut = { lean: implyLean + assignSuffix, latex: implyLatex };
                    declspec = declspec.lhs;
                    let collectedExplicit = null;
                    let name;
                    if (declspec instanceof L.LeanToken || declspec instanceof L.LeanProperty) {
                        name = declspec;
                        declspec = [];
                    } else if (
                        declspec &&
                        declspec.args &&
                        declspec.args.length >= 2 &&
                        !(declspec.args[0] && declspec.args[0] instanceof L.LeanParenthesis)
                    ) {
                        const dargs = declspec.args;
                        name = dargs[0];
                        const binders = dargs[1] && dargs[1].args ? dargs[1].args : (dargs.length > 2 ? dargs.slice(1) : []);
                        declspec = binders;
                    } else if (declspec && (declspec.lhs != null || declspec.args)) {
                        const collectParens = n => {
                            if (!n) return [];
                            if (n instanceof L.LeanParenthesis) return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(declspec);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = p.arg;
                                if (arg instanceof L.LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) lines[lines.length - 1] += ' :';
                            collectedExplicit = lines;
                        }
                        name = stmt.assignment;
                        declspec = [];
                    } else {
                        name = stmt.assignment;
                        declspec = [];
                    }
                    const instImplicit = [];
                    const implicit = [];
                    let explicit = [];
                    let given = null;
                    let default_ = [];
                    const decidables = [];
                    const typeVars = new Set();
                    const declList = declspec;
                    for (let i = 0; i < declList.length; ++i) {
                        const st = declList[i];
                        if (st instanceof L.LeanBracket) {
                            instImplicit.push(strStmt(st));
                            const ia = st.arg;
                            if (ia instanceof L.LeanArgsSpaceSeparated && ia.args.length === 2) {
                                const [l, r] = ia.args;
                                if (l instanceof L.LeanToken && l.text === 'Decidable' && r instanceof L.LeanToken)
                                    decidables.push(strStmt(r));
                            }
                            // `[Fintype S]`, `[NormedAddCommGroup α]`: class arguments are types
                            if (ia instanceof L.LeanArgsSpaceSeparated && ia.args[0] instanceof L.LeanToken && ia.args[0].text !== 'Decidable') {
                                for (const a of ia.args.slice(1))
                                    if (a instanceof L.LeanToken) typeVars.add(a.text);
                            }
                        } else if (st instanceof L.LeanBrace) {
                            st.toLatex(syntax);
                            implicit.push(st);
                        } else if (st instanceof L.LeanArgsSpaceSeparated) {
                            if (st.args.some((a) => a instanceof L.LeanParenthesis)) {
                                declList.splice(i, 1, ...st.args);
                                --i;
                            } else if (st.args[0] instanceof L.LeanBracket) {
                                instImplicit.push(strStmt(st));
                                for (const b of st.args) {
                                    const ia = b instanceof L.LeanBracket ? b.arg : null;
                                    if (ia instanceof L.LeanArgsSpaceSeparated && ia.args[0] instanceof L.LeanToken && ia.args[0].text !== 'Decidable') {
                                        for (const a of ia.args.slice(1))
                                            if (a instanceof L.LeanToken) typeVars.add(a.text);
                                    }
                                }
                            }
                            else if (st.args[0] instanceof L.LeanBrace) implicit.push(st);
                            else
                                error.push({
                                    code: strStmt(st),
                                    line: 0,
                                    info: `lemma ${strStmt(name)} is not well-defined`,
                                    type: 'linter',
                                });
                        } else if (st instanceof L.LeanLineComment) {
                            if (st.text === 'given') {
                                given = i + 1;
                                break;
                            }
                            if (implicit.length) implicit.push(strStmt(st));
                            else instImplicit.push(strStmt(st));
                        } else if (st instanceof L.LeanParenthesis) {
                            const inner = st.arg;
                            if (inner instanceof L.LeanColon) {
                                declList.splice(
                                    i,
                                    0,
                                    new L.LeanLineComment('given', st.indent, st.parent),
                                );
                                if (modify) modify.value = true;
                                ++i;
                            }
                            given = i;
                            break;
                        }
                    }
                    let givenOut = null;
                    if (given !== null) {
                        let givenSlice = declList.slice(given);
                        const latex = [];
                        let givenStart = null;
                        let givenStop = null;
                        let vars = null;
                        for (var i = 0; i < givenSlice.length; i++) {
                            const st = givenSlice[i];
                            if (st instanceof L.LeanParenthesis) {
                                const colon = st.arg;
                                if (colon instanceof L.LeanColon) {
                                    const prop = colon.rhs;
                                    if (vars == null) {
                                        vars = parseVars(implicit);
                                        for (const p of decidables) vars[p] = 'Prop';
                                        for (const v of Object.values(vars))
                                            if (typeof v === 'string' && /^[^\s()]+$/u.test(v) && v !== 'Prop') typeVars.add(v);
                                    }
                                    // A function-valued binder (`(«s.bvar» : ℕ → S)`) is data, not a
                                    // hypothesis. After givens have started, it ends the given run so the
                                    // binder moves to `default` with the other variables (trailing case).
                                    // Mid-run data between hypotheses still ends the given run too.
                                    const isData = looksLikeDataArrow(prop, vars, typeVars);
                                    if ((prop.isProp(vars) && !isData) || looksLikeClassHypothesis(colon.lhs, prop)) {
                                        latex.push([prop.toLatex(syntax), latexTag(strStmt(colon.lhs))]);
                                        if (givenStart === null) givenStart = i;
                                    } else if (givenStart !== null) {
                                        givenStop = i;
                                        break;
                                    }
                                } else if (colon instanceof L.LeanAssign) {
                                    break;
                                }
                            } else if (st.is_comment()) {
                                // Comments before the first hypothesis stay with `explicit`;
                                // a slot here would shift every given's LaTeX by one.
                                if (givenStart !== null) latex.push(null);
                            } else if (st instanceof L.LeanBrace) {
                                const pivot = i;
                                const par = new L.LeanParenthesis(st.arg, st.indent, st.parent);
                                par.is_closed = true;
                                givenSlice[pivot] = par;
                                break;
                            } else if (st instanceof L.LeanCaret) {
                                // skip
                            } else if (st instanceof L.LeanArgsSpaceSeparated) {
                                givenSlice.splice(i, 1, ...st.args);
                                --i;
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
                                    ? `${pair[0]}\\tag*{\$${pair[1]}\$}`
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

                    const proof = innerAssign.rhs;
                    let proofOut;
                    let proofNode = proof;
                    if (
                        assignIdx >= 0 &&
                        !(proof instanceof L.LeanBy || proof instanceof L.LeanCalc) &&
                        (proof instanceof L.LeanCaret || !(proof.args && proof.args.length))
                    ) {
                        let end = assignIdx + 1;
                        for (; end < args.length; ++end) {
                            const x = args[end];
                            if (x instanceof L.LeanLineComment && /^(created|updated)\s/i.test(String(x.text || '')))
                                break;
                        }
                        proofNode = { args: args.slice(assignIdx + 1, end) };
                    }
                    syntax.letBindings = buildLetBindings(imply.length ? imply : flatImplyStmts);
                    if (by) {
                        proofOut = { [by]: leanModuleMergeProof(proofNode.arg ?? proofNode, echo, syntax) };
                    } else {
                        proofOut = leanModuleMergeProof(proofNode, echo, syntax);
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
                } else if (declspec && (typeof declspec.toLatex === 'function' || flatImplyStmts.length > 0)) {
                    const proof0 = innerAssign.rhs;
                    const by = proof0 instanceof L.LeanBy? 'by' : proof0 instanceof L.LeanCalc? 'calc': '';

                    let simpleExplicit = flatExplicit;
                    let simpleName = null;
                    let implyNode = declspec;
                    if (declspec instanceof L.LeanColon && declspec.lhs && !flatExplicit) {
                        const inner = declspec.lhs;

                        if (inner.lhs instanceof L.LeanColon) {
                            const binderNode = inner.lhs.lhs;
                            const collectParens = n => {
                                if (!n) return [];
                                if (n instanceof L.LeanParenthesis) return [n];
                                const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                                return a.flatMap(collectParens);
                            };
                            const parens = collectParens(binderNode);
                            if (parens.length > 0) {
                                const lines = parens.map((p) => {
                                    const arg = p.arg;
                                    if (arg instanceof L.LeanColon && arg.lhs && arg.rhs)
                                        return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                    return strStmt(p);
                                });
                                if (lines.length) {
                                    lines[lines.length - 1] += ' :';
                                    simpleExplicit = lines.join('\n');
                                }
                            }

                            const innerLhs = inner.lhs;
                            implyNode =
                                (innerLhs &&
                                    innerLhs.rhs &&
                                    (innerLhs.rhs instanceof L.LeanStatements || innerLhs.rhs instanceof L.LeanArgsNewLineSeparated))
                                    ? innerLhs.rhs
                                    : inner.rhs || declspec;
                        } else if (declspec.rhs) {
                            // Standard `name (binders) : proposition := by …`
                            // binders live in the colon LHS, proposition in RHS.
                            const nameNode =
                                (inner.lhs instanceof L.LeanToken || inner.lhs instanceof L.LeanProperty)
                                    ? inner.lhs
                                    : (inner instanceof L.LeanToken || inner instanceof L.LeanProperty)
                                        ? inner
                                        : null;
                            if (nameNode) simpleName = nameNode;
                            const collectParens = n => {
                                if (!n) return [];
                                if (n instanceof L.LeanParenthesis) return [n];
                                const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                                return a.flatMap(collectParens);
                            };
                            const parens = collectParens(nameNode === inner ? null : inner);
                            if (parens.length > 0) {
                                const lines = parens.map((p) => {
                                    const arg = p.arg;
                                    if (arg instanceof L.LeanColon && arg.lhs && arg.rhs)
                                        return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                    return strStmt(p);
                                });
                                if (lines.length) {
                                    lines[lines.length - 1] += ' :';
                                    simpleExplicit = lines.join('\n');
                                }
                            }
                            implyNode = declspec.rhs;
                        }
                    }
                    let implyOut;
                    if (flatImplyStmts && flatImplyStmts.length > 0) {
                        const imply = [...flatImplyStmts, assignment.lhs];
                        markRandomVarSequence(imply, flatRvNames);
                        const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                        let implyLatex;
                        if (imply.length > 1 && imply[0] instanceof L.Lean_let) {
                            implyLatex = implyLetAlignLatex(imply, syntax);
                        } else {
                            implyLatex = imply
                                .map((st) => implyConclusionLatex(st, syntax))
                                .join('\n');
                        }

                        implyOut = { lean: implyLean + ' :=' + (by ? ` ${by}` : ''), latex: implyLatex };
                    } else {
                        markRandomVarSequence([implyNode], flatRvNames);
                        const implyLean = unindentTwo(strStmt(implyNode)) + ' :=' + (by ? ` ${by}` : '');
                        const implyLatex = implyConclusionLatex(implyNode, syntax);
                        implyOut = { lean: implyLean, latex: implyLatex };
                    }
                    syntax.letBindings = buildLetBindings(flatImplyStmts ?? []);
                    const proof = innerAssign.rhs;
                    let proofOut;
                    const proofArg = proof && typeof proof === 'object' && 'arg' in proof ? proof.arg : proof;
                    const hasProofArgs = proofArg && typeof proofArg === 'object' && Array.isArray(proofArg.args);
                    if (by) {
                        proofOut = { [by]: hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [] };
                    } else {
                        proofOut = hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [{ lean: strStmt(proof || ''), latex: null }];
                    }
                    let attribute = extractAttribute(stmt.attribute);
                    const name = simpleName ?? stmt.assignment;
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
        } else if (stmt instanceof L.Lean_def) {
            preamble.push(strStmt(stmt));
        } else if (stmt instanceof L.Lean_open) {
            let o = stmt.arg;
            if (o instanceof L.LeanArgsSpaceSeparated) {
                if (o.args.length === 2 && o.args[1] instanceof L.LeanParenthesis) {
                    const defs = o.args[1].arg;
                    open.push({
                        [strStmt(o.args[0])]:
                            defs instanceof L.LeanArgsSpaceSeparated
                                ? defs.args.map((a) => strStmt(a))
                                : [strStmt(defs.arg)],
                    });
                } else open.push(o.args.map((a) => strStmt(a)).filter((s) => s.trim()));
            } else open.push([strStmt(o.text)]);
        } else if (stmt instanceof L.Lean_set_option) {
            const a = stmt.arg;
            if (a instanceof L.LeanArgsSpaceSeparated) set_option.push(a.args.map((x) => strStmt(x)));
        } else if (stmt instanceof L.LeanLineComment) {
            const m = /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.exec(stmt.text);
            if (m) date[m[1]] = m[2];
            else comment = stmt.text;
        } else if (stmt instanceof L.LeanBlockComment) {
            comment = stmt.text;
        }
    }

    return {
        imports: $import,
        open,
        set_option,
        preamble,
        lemma,
        date,
        error,
    };
}
export class LeanModule extends LeanStatements {
    static { this.register(); }

    get root() {
        return this;
    }

    get stack_priority() {
        return -3;
    }

    array_push(vars, lhs, rhs) {
        arrayPushVars(vars, lhs, rhs);
    }

    create_property(module) {
        const parts = String(module).split('.');
        return parts.reduce((carry, token) => {
            const t = new L.LeanToken(token, 0, 0);
            return carry ? new L.LeanProperty(carry, t, 0, 0) : t;
        }, null);
    }

    decode(json, latex) {
        const keys = Object.keys(json);
        if (!keys.length) return;
        const line = keys[0];
        const latexFormat = json[line];
        if (Object.prototype.hasOwnProperty.call(latex, line)) {
            if (!Array.isArray(latex[line])) latex[line] = [latex[line]];
            latex[line].push(latexFormat);
        } else {
            latex[line] = latexFormat;
        }
    }

    echo() {
        this.import('sympy.printing.echo');
        const {args} = this;
        for (let i = 0; i < args.length; i++) args[i].echo();
    }

    echo2vue(_leanFile) {
        throw new Error(
            'LeanModule.echo2vue runs only on the Node server (see server/lean/echo2vue.mjs `runEcho2Vue`).',
        );
    }

    /**
     * After writing `*.echo.lean` with inflated maxHeartbeats (×5 for Lean server),
     * revert those nodes in the AST so `render2vue` reports the original values.
     */
    restoreMaxHeartbeats() {
        for (const node of this.args) {
            if (node instanceof L.Lean_set_option) {
                const arg = node.arg;
                if (arg instanceof L.LeanArgsSpaceSeparated && arg.args.length === 2) {
                    const [nameTok, valTok] = arg.args;
                    if (
                        nameTok instanceof L.LeanToken &&
                        valTok instanceof L.LeanToken &&
                        nameTok.text === 'maxHeartbeats'
                    ) {
                        const v = parseInt(String(valTok.text), 10);
                        if (!Number.isNaN(v)) {
                            valTok.text = String(Math.floor(v / 5));
                            break;
                        }
                    }
                }
            }
        }
    }

    import(module) {
        this.args.unshift(new L.Lean_import(this.create_property(module), 0, 0));
    }

    /**
     * Port of `LeanModule::insert`.
     * @param {LeanCaret} caret
     * @param {string | typeof Lean} func class name or constructor
     */
    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof L.LeanCaret) {
            const Ctor = typeof func === 'string' ? L[func] : func;
            this.push(new Ctor(caret, this.indent, caret.level));
            return caret;
        }
        return caret;
    }

    parse_vars(implicit) {
        return parseVars(implicit);
    }

    parse_vars_default(defaultList) {
        const vars = [];
        for (const parenthesis of defaultList) {
            if (parenthesis instanceof L.LeanParenthesis) {
                const colon = parenthesis.arg;
                if (colon instanceof L.LeanColon) arrayPushVars(vars, colon.lhs, colon.rhs);
            }
        }
        return vars;
    }

    render2vue(echo, modify = null, syntax = {}) {
        return leanModuleRender2vue(this, echo, modify, syntax);
    }

    static merge_proof(proof, echo, syntax = {}) {
        return leanModuleMergeProof(proof, echo, syntax);
    }

    leanModuleStrSegments() {
        const args = this.args;
        /** @type {string[]} */
        const parts = [];
        const skip = new Set();
        const indentText = (s, indent) => {
            if (indent <= 0) return s;
            const pad = ' '.repeat(indent);
            return s
                .split('\n')
                .map((line) => (line === '' ? line : pad + line))
                .join('\n');
        };
        for (let i = 0; i < args.length; i++) {
            if (skip.has(i)) continue;
            const a = args[i];
            if (a == null) continue;
            if (a instanceof L.LeanCaret) {
                parts.push('');
                continue;
            }
            if (a instanceof L.Lean_def) {
                const asn = a.assignment;
                if (asn instanceof L.LeanAssign && asn.rhs instanceof L.LeanCaret) {
                    const tail = consumeEchoAssignProofTail(args, i + 1, indentText);
                    if (tail) {
                        for (let k = i + 1; k <= tail.endJ; k++) skip.add(k);
                        const acc = a.accessibility === 'public' ? '' : `${a.accessibility} `;
                        const kw = `${acc}${a.func} `;
                        const head = a.attribute ? `${String(a.attribute)}\n${kw}` : kw;
                        const asnPad = ' '.repeat(Math.max(0, asn.indent ?? 0));
                        let block = `${head}${asnPad}${String(asn.lhs)} :=`;
                        for (const c of tail.cmts) block += `\n${String(c)}`;
                        block += `\n${tail.proofStr}`;
                        parts.push(block);
                        continue;
                    }
                }
            }
            if (a instanceof L.LeanAssign && a.rhs instanceof L.LeanCaret) {
                const tail = consumeEchoAssignProofTail(args, i + 1, indentText);
                if (tail) {
                    for (let k = i + 1; k <= tail.endJ; k++) skip.add(k);
                    const asnPad = ' '.repeat(Math.max(0, a.indent ?? 0));
                    let block = `${asnPad}${String(a.lhs)} :=`;
                    for (const c of tail.cmts) block += `\n${String(c)}`;
                    block += `\n${tail.proofStr}`;
                    parts.push(block);
                    continue;
                }
            }
            if (a instanceof L.LeanTactic) {
                const next = i + 1 < args.length ? args[i + 1] : null;
                let danglingStc = false;
                for (let k = 0; k < a.args.length; k++) {
                    const x = a.args[k];
                    if (x instanceof L.LeanSequentialTacticCombinator && x.arg instanceof L.LeanCaret) {
                        danglingStc = true;
                        break;
                    }
                }
                if (danglingStc && next instanceof L.LeanTacticBlock) {
                    skip.add(i + 1);
                    const indent = Math.max(a.indent ?? 0, next.indent ?? 0);
                    const as = String(a);
                    const ns = String(next);
                    const join = as.endsWith('\n') ? '' : '\n';
                    parts.push(indentText(`${as}${join}${ns}`, indent));
                    continue;
                }
            }
            if (a instanceof L.LeanColon && a.parent === this) {
                const indent = a.indent ?? 0;
                if (indent > 0) {
                    let k = i + 1;
                    while (k < args.length && args[k] instanceof L.LeanCaret) k++;
                    let next = args[k];
                    const echoTail =
                        next instanceof L.LeanAssign &&
                        next.rhs instanceof L.LeanCaret &&
                        consumeEchoAssignProofTail(args, k + 1, indentText);
                    let assignAfterColon = next;
                    if (!(next instanceof L.LeanAssign)) {
                        let j = k;
                        while (j < args.length) {
                            const x = args[j];
                            if (x instanceof L.LeanCaret) {
                                j++;
                                continue;
                            }
                            if (x instanceof L.Lean_land) {
                                j++;
                                continue;
                            }
                            if (x instanceof L.LeanAssign) {
                                assignAfterColon = x;
                                break;
                            }
                            break;
                        }
                    }
                    let prevIdx = i - 1;
                    while (prevIdx >= 0) {
                        const p = args[prevIdx];
                        if (p == null || p instanceof L.LeanCaret) {
                            prevIdx--;
                            continue;
                        }
                        if (
                            p instanceof L.LeanBrace ||
                            p instanceof L.LeanBracket ||
                            p instanceof L.LeanParenthesis ||
                            p instanceof L.LeanLineComment ||
                            p instanceof L.LeanBlockComment
                        ) {
                            prevIdx--;
                            continue;
                        }
                        break;
                    }
                    const lemmaColonMatchBy =
                        prevIdx >= 0 &&
                        args[prevIdx] instanceof L.Lean_lemma &&
                        assignAfterColon instanceof L.LeanAssign &&
                        assignAfterColon.rhs instanceof L.LeanBy &&
                        (assignAfterColon.lhs instanceof L.Lean_match ||
                            assignAfterColon.lhs instanceof L.LeanParenthesis);
                    if (echoTail || lemmaColonMatchBy) {
                        const lines = String(a).split('\n');
                        if (lines[0] !== '') lines[0] = ' '.repeat(indent) + lines[0];
                        parts.push(lines.join('\n'));
                        continue;
                    }
                }
            }
            let out = String(a);
            if (a instanceof L.LeanTactic && (a.indent ?? 0) === 0) {
                let p = i - 1;
                while (p >= 0 && (args[p] instanceof L.LeanCaret || args[p] == null || skip.has(p))) p--;
                const prev = p >= 0 ? args[p] : null;
                const indent = prev instanceof L.Lean_let ? prev.indent ?? 0 : 0;
                if (indent > 0) out = ' '.repeat(indent) + out;
            }
            parts.push(out);
        }
        return parts;
    }

    strFormat() {
        this._moduleStrSegs = this.leanModuleStrSegments();
        const n = this._moduleStrSegs.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join('\n');
    }

    strArgs() {
        const segs = this._moduleStrSegs ?? this.leanModuleStrSegments();
        delete this._moduleStrSegs;
        return segs;
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    // insert_colon, insert_if, insert_left, insert_newline, insert_space, insert_tactic: inherit `LeanStatements` / `Lean`.
}
