/**
 * Open-prefix lemma navigation: short names after `open Foo` resolve to Foo.short.
 * Run: node scripts/test-open-prefix-nav.mjs
 */
import assert from 'assert';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { disambiguateModule } from '../server/lean/disambiguate.mjs';
import {
	dottedIdentifierAt,
	flattenOpens,
	isOpenStrippedLemmaName,
	lemmaSuffixPrefix,
	moduleLinkTarget,
	moduleRegexpBody,
	openNamespaceCandidates,
	pickLatestOpen,
	qualifyOpenedModule,
	regexpSectionNames,
	resolveOpenedImport,
} from '../static/js/codeMirrorEditor.js';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const sections = new Set(
	fs.readdirSync(path.join(root, 'Lemma'), { withFileTypes: true })
		.filter((d) => d.isDirectory())
		.map((d) => d.name),
);

function header(rel) {
	const text = fs.readFileSync(path.join(root, rel), 'utf8');
	const opens = [];
	const imports = [];
	for (const line of text.split('\n')) {
		const t = line.trim();
		if (t.startsWith('import '))
			imports.push(t.slice('import '.length).trim());
		else if (t.startsWith('open scoped'))
			continue;
		else if (t.startsWith('open '))
			opens.push(...t.slice('open '.length).trim().split(/\s+/));
		else if (t)
			break;
	}
	return { opens, imports };
}

function resolveShort(short, opens, imports) {
	const imported = resolveOpenedImport(short, opens, imports);
	if (imported)
		return imported;
	const candidates = openNamespaceCandidates(short, opens, (name) => sections.has(name));
	const found = candidates.filter((c) => disambiguateModule(c.rest, c.section) === c.section);
	return pickLatestOpen(found, opens);
}

function headIsSection(name) {
	const m = name.match(/^([\w'!₀-₉]+)\.(.+)/);
	return !!(m && sections.has(m[1]));
}

const gradShort = 'GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico';
const gradFull = `Random.${gradShort}`;

function f3Url(lookupResult) {
	const target = moduleLinkTarget(lookupResult);
	if (!target)
		return null;
	return `?${target[0]}=${target[1]}`;
}

for (const miss of [undefined, null, 0, '', [], {}, 'Random.GradV'])
	assert.equal(f3Url(miss), null);
assert.equal(f3Url(['module', gradFull]), `?module=${gradFull}`);

// axiom.lemma regexp miss used to `return;` (undefined). Destructuring that throws.
for (const rows of [undefined, null, 0, '', [], {}])
	assert.deepEqual(regexpSectionNames(rows), []);
assert.deepEqual(regexpSectionNames([['Random'], ['Random'], ['']]), ['Random']);
assert.throws(() => {
	var [table, module] = undefined;
	return table + module;
}, TypeError);
for (const rows of [undefined, null, 0, []]) {
	const names = regexpSectionNames(rows);
	const lookup = names.length ? ['module', `${names[0]}.${gradShort}`] : null;
	assert.equal(f3Url(lookup), null);
}

assert.deepEqual(flattenOpens([['Random']]), ['Random']);
assert.deepEqual(flattenOpens(['Random']), ['Random']);
assert.deepEqual(flattenOpens('[["Filter","Random"]]'), ['Filter', 'Random']);
assert.deepEqual(flattenOpens([['scoped', 'RealInnerProductSpace'], ['Random']]), ['RealInnerProductSpace', 'Random']);

const line = `rw [${gradShort} h₀ h₃ h₄ h₅]`;
const mid = line.indexOf('AddSum') + 2;
const atMiddle = dottedIdentifierAt(line, mid);
assert.equal(atMiddle.module, gradShort);
assert.ok(atMiddle.postfix.startsWith(' '));
const atEnd = dottedIdentifierAt(line, line.indexOf('In_Ico') + 3);
assert.equal(atEnd.module, gradShort);

assert.equal(
	resolveOpenedImport(gradShort, flattenOpens([['Random']]), [`Lemma.${gradFull}`]),
	gradFull,
);

let disambiguateCalls = 0;
assert.equal(
	await qualifyOpenedModule(
		gradShort,
		'[["Random"]]',
		[`Lemma.${gradFull}`],
		() => {
			disambiguateCalls++;
			return '';
		},
		() => false,
	),
	gradFull,
);
assert.equal(disambiguateCalls, 0);

let sqlHits = 0;
assert.equal(
	await qualifyOpenedModule(
		gradShort,
		[['Random']],
		[],
		(rest, section) => {
			assert.equal(section, 'Random');
			assert.equal(rest, gradShort);
			return 'Random';
		},
		() => false,
	),
	gradFull,
);
assert.equal(sqlHits, 0);
assert.equal(f3Url(['module', gradFull]), `?module=${gradFull}`);

assert.equal(
	await qualifyOpenedModule(gradShort, ['Random'], [], () => '', (name) => name === 'Random'),
	null,
);

assert.equal(isOpenStrippedLemmaName('h₀'), false);
assert.equal(isOpenStrippedLemmaName('μ.bind'), false);
assert.equal(isOpenStrippedLemmaName(gradShort), true);
assert.equal(isOpenStrippedLemmaName('of.Any_All'), true);

assert.equal(lemmaSuffixPrefix(gradFull, gradShort), 'Random');
assert.equal(lemmaSuffixPrefix(gradFull, gradFull), null);
assert.equal(
	resolveOpenedImport(gradShort, ['MeasureTheory', 'Random'], [`Lemma.${gradFull}`]),
	gradFull,
);
assert.equal(
	resolveOpenedImport(gradShort, ['MeasureTheory'], [`Lemma.${gradFull}`]),
	null,
);

const gradBody = moduleRegexpBody(gradShort);
assert.equal(gradBody, gradShort.replace(/\./g, '\\.'));
assert.equal(gradBody.includes('.'), true);
assert.equal(/(?<!\\)\./.test(gradBody), false);

const summable = 'All_Summable.of.Summable_Integral.All_AeGe_0.All_Integrable';
assert.equal(disambiguateModule(summable), 'Random');
assert.equal(disambiguateModule(summable, 'Random'), 'Random');
assert.equal(disambiguateModule(summable, 'Filter'), '');
assert.equal(disambiguateModule(summable, 'NotASection'), '');

const tendstoFile = 'Lemma/Random/All_Tendsto_0/of/Any_All_AeLeCondExp/Summable/TendstoSum/All_Gt_0/All_AeGe_0/All_Integrable/StronglyAdapted.lean';
const tendsto = header(tendstoFile);
const summableShort = summable;
assert.equal(headIsSection(`Random.${summableShort}`), true);
assert.equal(headIsSection(summableShort), false);
assert.equal(resolveShort(summableShort, tendsto.opens, tendsto.imports), `Random.${summableShort}`);
assert.equal(resolveShort(summableShort, tendsto.opens, []), `Random.${summableShort}`);
assert.equal(
	await qualifyOpenedModule(
		summableShort,
		tendsto.opens,
		[],
		(rest, section) => disambiguateModule(rest, section),
		() => false,
	),
	`Random.${summableShort}`,
);

const eq0 = 'Eq_0.of.Tendsto.Summable_Mul.All_Ge_0.TendstoSum.All_Gt_0';
assert.equal(resolveShort(eq0, tendsto.opens, tendsto.imports), `Real.${eq0}`);
assert.equal(disambiguateModule(eq0, 'Real'), 'Real');
assert.equal(disambiguateModule(eq0, 'Random'), '');

const nestedShort = 'of.Any_All_AeLeCondExp.Summable.TendstoSum.All_Gt_0.All_AeGe_0.All_Integrable.StronglyAdapted';
assert.equal(
	resolveShort(nestedShort, ['Random.All_Tendsto_0'], []),
	`Random.All_Tendsto_0.${nestedShort}`,
);

const iterates = 'Lemma/Iterates/AeTendsto/of/LyapunovFunction/Measurable/Measurable/LipschitzWith/Eq/Adapted/Any_Ge_0AndAeAll_LeNormMulMulSquare/All_AeEqCondExp_0/Adapted/Any_Ge_0AndAeAll_LeNormMulMul/Iterates.lean';
const iteratesHead = header(iterates);
const cond = 'CondExpInner.ae.Inner_CondExp.of.All_AEStronglyMeasurable.All_Integrable_Mul.Integrable';
const lim = 'All_Tendsto_0.of.Any_All_AeLeCondExp.Summable.TendstoSum.All_Gt_0.All_AeGe_0.All_Integrable.StronglyAdapted';
assert.equal(resolveShort(cond, iteratesHead.opens, iteratesHead.imports), `Random.${cond}`);
assert.equal(resolveShort(lim, iteratesHead.opens, iteratesHead.imports), `Random.${lim}`);

const kernel = 'Lemma/Kernel/AeEqCondExp/of/AeAeEqCondExp/Le/Integrable_Bind/Integrable_Bind/StronglyMeasurable.lean';
const kernelHead = header(kernel);
const integral = 'Integral.eq.Integral_Integral.of.Integrable_Bind';
assert.equal(headIsSection(`Kernel.${integral}`), true);
assert.equal(headIsSection(integral), false);
assert.equal(resolveShort(integral, kernelHead.opens, kernelHead.imports), `Kernel.${integral}`);
assert.equal(disambiguateModule('In_Ico', 'Set'), 'Set');
assert.equal(disambiguateModule('In_Ico', 'Finset'), '');
assert.equal(disambiguateModule(integral), 'Kernel');
assert.equal(disambiguateModule(integral, 'Kernel'), 'Kernel');

assert.equal(
	pickLatestOpen(
		[
			{ ns: 'Random', full: 'Random.Name' },
			{ ns: 'Real', full: 'Real.Name' },
		],
		['Random', 'Real'],
	),
	'Real.Name',
);

console.log('open-prefix navigation tests passed');
