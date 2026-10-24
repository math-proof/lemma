/**
 * `isNewInGit` / `date-created-today`: a `mv` of an already-dated lemma is not a new file.
 * Run: `node mjs/lean/lint/isNewInGit.test.mjs`
 */
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { isNewInGit, lintLean } from './index.mjs';

const git = (cwd, args) => execFileSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });

function lemma(created, extra = '') {
    return [
        'import Lemma.Dummy',
        '',
        '',
        '/-- test -/',
        '@[simp]',
        'lemma Foo : True := by',
        '  trivial',
        extra,
        '',
        '',
        `-- created on ${created}`,
        '',
    ].join('\n');
}

function setupRepo() {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'isNewInGit-'));
    git(root, ['init']);
    git(root, ['config', 'user.email', 'test@example.com']);
    git(root, ['config', 'user.name', 'test']);
    git(root, ['config', 'commit.gpgsign', 'false']);
    return root;
}

let failed = 0;
function check(name, cond) {
    if (!cond) {
        failed++;
        console.error(`FAIL ${name}`);
    } else {
        console.log(`ok   ${name}`);
    }
}

{
    const root = setupRepo();
    const oldRel = 'Lemma/Random/Measurable_A.lean';
    const newRel = 'Lemma/Random/Measurable/of/All_Eq.lean';
    const src = lemma('2026-10-07');
    fs.mkdirSync(path.dirname(path.join(root, oldRel)), { recursive: true });
    fs.writeFileSync(path.join(root, oldRel), src);
    git(root, ['add', oldRel]);
    git(root, ['commit', '-m', 'add lemma']);
    fs.mkdirSync(path.dirname(path.join(root, newRel)), { recursive: true });
    fs.renameSync(path.join(root, oldRel), path.join(root, newRel));
    check('rename dest is not new (D + ??, same blob)', isNewInGit(path.join(root, newRel)) === false);
    const warns = lintLean(src, { file: newRel, root, today: '2026-10-10', isNew: isNewInGit(path.join(root, newRel)) })
        .filter((w) => w.rule === 'date-created-today');
    check('rename does not fire date-created-today', warns.length === 0);
    fs.rmSync(root, { recursive: true, force: true });
}

{
    const root = setupRepo();
    const oldRel = 'Lemma/Random/Measurable_A.lean';
    const newRel = 'Lemma/Random/Measurable/of/All_Eq.lean';
    const oldSrc = lemma('2026-10-07', '  -- Random.Measurable_A');
    const newSrc = lemma('2026-10-07', '  -- Random.Measurable.of.All_Eq');
    fs.mkdirSync(path.dirname(path.join(root, oldRel)), { recursive: true });
    fs.writeFileSync(path.join(root, oldRel), oldSrc);
    git(root, ['add', oldRel]);
    git(root, ['commit', '-m', 'add lemma']);
    fs.mkdirSync(path.dirname(path.join(root, newRel)), { recursive: true });
    fs.renameSync(path.join(root, oldRel), path.join(root, newRel));
    fs.writeFileSync(path.join(root, newRel), newSrc);
    check('rename dest is not new after import/module rewrite', isNewInGit(path.join(root, newRel)) === false);
    fs.rmSync(root, { recursive: true, force: true });
}

{
    // rename.sh path shortening + substantial body edit (overlap < 0.7): still same lemma
    const root = setupRepo();
    const oldRel = 'Lemma/Measure/Measure/eq/Count/of/EqMeasureCount/EqMeasureCount.lean';
    const newRel = 'Lemma/Measure/Measure/eq/Count.lean';
    const oldSrc = [
        'import Lemma.Measure.Count.eq.ProdCountS',
        'import sympy.stats.rv',
        'open MeasureTheory',
        '',
        '',
        '/-- old -/',
        '@[path]',
        'private lemma main',
        '  [ReferenceMeasure α] [ReferenceMeasure β]',
        '  (hα : ReferenceMeasure.measure (α := α) = Measure.count)',
        '  (hβ : ReferenceMeasure.measure (α := β) = Measure.count) :',
        '  ReferenceMeasure.measure (α := α × β) = Measure.count := by',
        '  rw [hα, hβ, Measure.Count.eq.ProdCountS]',
        '',
        '',
        '-- created on 2026-10-04',
        '',
    ].join('\n');
    const newSrc = [
        'import Lemma.Measure.Count.eq.ProdCountS',
        'import sympy.stats.rv',
        'open MeasureTheory Measure',
        '',
        '',
        '/-- new: CountableMeasure -/',
        '@[path]',
        'private lemma main',
        '  [CountableMeasure α] [CountableMeasure β]',
        '  [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β] :',
        '  ReferenceMeasure.measure (α := α × β) = Measure.count := by',
        '  show (ReferenceMeasure.measure : Measure α).prod (ReferenceMeasure.measure : Measure β) = _',
        '  rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS]',
        '',
        '',
        '-- created on 2026-10-04',
        '-- updated on 2026-10-22',
        '',
    ].join('\n');
    fs.mkdirSync(path.dirname(path.join(root, oldRel)), { recursive: true });
    fs.writeFileSync(path.join(root, oldRel), oldSrc);
    git(root, ['add', oldRel]);
    git(root, ['commit', '-m', 'add lemma']);
    fs.mkdirSync(path.dirname(path.join(root, newRel)), { recursive: true });
    fs.renameSync(path.join(root, oldRel), path.join(root, newRel));
    fs.writeFileSync(path.join(root, newRel), newSrc);
    check('rename.sh shorten + body rewrite is not new', isNewInGit(path.join(root, newRel)) === false);
    const warns = lintLean(newSrc, {
        file: newRel,
        root,
        today: '2026-10-22',
        isNew: isNewInGit(path.join(root, newRel)),
    }).filter((w) => w.rule === 'date-created-today');
    check('rename.sh shorten + body rewrite: no date-created-today', warns.length === 0);
    fs.rmSync(root, { recursive: true, force: true });
}

{
    const root = setupRepo();
    const rel = 'Lemma/Foo/Bar.lean';
    fs.mkdirSync(path.dirname(path.join(root, rel)), { recursive: true });
    fs.writeFileSync(path.join(root, '.gitignore'), '');
    git(root, ['add', '.gitignore']);
    git(root, ['commit', '-m', 'init']);
    fs.writeFileSync(path.join(root, rel), lemma('2026-10-07'));
    check('truly new ?? file is new', isNewInGit(path.join(root, rel)) === true);
    const warns = lintLean(lemma('2026-10-07'), { file: rel, root, today: '2026-10-10', isNew: true })
        .filter((w) => w.rule === 'date-created-today');
    check('truly new file still warns date-created-today', warns.length === 1);
    fs.rmSync(root, { recursive: true, force: true });
}

{
    const root = setupRepo();
    const tracked = 'Lemma/A/All_Eq.lean';
    const other = 'Lemma/B/All_Eq.lean';
    fs.mkdirSync(path.dirname(path.join(root, tracked)), { recursive: true });
    fs.writeFileSync(path.join(root, tracked), lemma('2026-01-01'));
    git(root, ['add', tracked]);
    git(root, ['commit', '-m', 'tracked All_Eq']);
    fs.mkdirSync(path.dirname(path.join(root, other)), { recursive: true });
    fs.writeFileSync(path.join(root, other), lemma('2026-10-07'));
    check('basename collision does not mark tracked file new', isNewInGit(path.join(root, tracked)) === false);
    check('basename collision: sibling ?? All_Eq.lean is still new', isNewInGit(path.join(root, other)) === true);
    fs.rmSync(root, { recursive: true, force: true });
}

{
    // Radical lemmaPath rename: HEAD still has a tiny axiom stub (low line overlap), modules do not
    // share a prefix — keep `-- created on` via unique same-date delete match.
    const root = setupRepo();
    const oldRel = 'Lemma/Random/Eq/ArgMax/Mul/Prod_ProbCond/of/Ne_0/Eq.lean';
    const newRel = 'Lemma/Random/GetArgMaxProbCond/eq/ArgMax/of/NeProbJoint__0/All_CondIndep.lean';
    const stub = [
        'import Lemma.Dummy',
        '',
        '',
        'axiom Random.Eq.ArgMax.Mul.Prod_ProbCond.of.Ne_0.Eq : True',
        '',
        '',
        '-- created on 2021-07-21',
        '',
    ].join('\n');
    const full = [
        'import Lemma.Dummy',
        'open Fun',
        '',
        '',
        '/-- naive Bayes argmax -/',
        '@[path]',
        'private lemma main',
        '  [NeZero (n : ℕ)] {m : ℕ}',
        '  {x : ℕ → α} {y : ℕ → β} :',
        '  True := by',
        '  trivial',
        '',
        '',
        '-- created on 2021-07-21',
        '-- updated on 2026-10-22',
        '',
    ].join('\n');
    fs.mkdirSync(path.dirname(path.join(root, oldRel)), { recursive: true });
    fs.writeFileSync(path.join(root, oldRel), stub);
    git(root, ['add', oldRel]);
    git(root, ['commit', '-m', 'axiom stub']);
    fs.mkdirSync(path.dirname(path.join(root, newRel)), { recursive: true });
    fs.renameSync(path.join(root, oldRel), path.join(root, newRel));
    fs.writeFileSync(path.join(root, newRel), full);
    check('radical rename + axiom stub HEAD is not new', isNewInGit(path.join(root, newRel)) === false);
    const warns = lintLean(full, {
        file: newRel,
        root,
        today: '2026-10-22',
        isNew: isNewInGit(path.join(root, newRel)),
    }).filter((w) => w.rule === 'date-created-today');
    check('radical rename: no date-created-today', warns.length === 0);
    fs.rmSync(root, { recursive: true, force: true });
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}
console.log('all passed');
