import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry14Bernoullipolymult
open scoped Nat Real BigOperators Interval
open Asymptotics Filter Finset Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry14Bernoullipolymult


/--
[chapter7StieltjesA_eq_entry14Bernoulliasymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean)
-/
@[path]
private lemma chapter7StieltjesA_eq_entry14Bernoulliasymptotic_eq
  :
-- imply
  chapter7StieltjesA = Entry14Bernoulliasymptotic.chapter7StieltjesA := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoullipolymult.chapter7StieltjesA_eq_entry14Bernoulliasymptotic

/--
[summable_chapter7Entry14Term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean)
-/
@[path]
private lemma summable_chapter7Entry14Term_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  Summable (chapter7Entry14Term x) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoullipolymult.summable_chapter7Entry14Term x hx

/--
[chapter7StieltjesApprox_eq_entry13Bernoullipolyadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean)
-/
@[path]
private lemma chapter7StieltjesApprox_eq_entry13Bernoullipolyadd_eq
  :
-- imply
  chapter7StieltjesApprox = Entry13Bernoullipolyadd.chapter7StieltjesApprox := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoullipolymult.chapter7StieltjesApprox_eq_entry13Bernoullipolyadd

/--
[ramanujan_part1_ch7_entry14_bernoullipolymult](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry14_bernoullipolymult_eq
  {a0 : ℝ}
  {c : ℕ → ℝ}
-- given
  (ha0 : Tendsto chapter7Entry14A0Approx atTop (𝓝 a0))
  (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
-- imply
  (∀ x : ℝ, 0 < x → Summable (chapter7Entry14Term x)) ∧
    ∀ N : ℕ,
    IsBigO (nhdsWithin 0 (Set.Ioi 0))
    (fun x : ℝ => chapter7Entry14Sum x - chapter7Entry14Approx a0 c N x)
    (fun x : ℝ => x ^ (2 * N + 1)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoullipolymult.ramanujan_part1_ch7_entry14_bernoullipolymult a0 c ha0 hc


-- created on 2026-10-20
