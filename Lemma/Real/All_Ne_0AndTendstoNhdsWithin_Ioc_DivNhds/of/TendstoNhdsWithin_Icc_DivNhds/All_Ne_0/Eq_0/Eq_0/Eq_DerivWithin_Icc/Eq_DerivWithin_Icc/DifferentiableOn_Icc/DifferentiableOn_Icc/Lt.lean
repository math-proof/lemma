import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_10_5
open Chapter9
open Chapter10
open Filter
open Filter.Tendsto


/--
[_root_.Filter.Tendsto.of_div'](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_5.lean)
-/
@[path]
private lemma main
  {a b L:ℝ}
  {f g f' g': ℝ → ℝ}
-- given
  (hab: a < b)
  (hf: DifferentiableOn ℝ f (.Icc a b))
  (hg: DifferentiableOn ℝ g (.Icc a b))
  (hf': f' = derivWithin f (.Icc a b))
  (hg': g' = derivWithin g (.Icc a b))
  (hfa: f a = 0)
  (hga: g a = 0)
  (hgnon: ∀ x ∈ Set.Icc a b, g' x ≠ 0)
  (hderiv: (nhdsWithin a (.Icc a b)).Tendsto (fun x ↦ f' x / g' x) (nhds L)) :
-- imply
  (∀ x ∈ Set.Ioc a b, g x ≠ 0) ∧
    (nhdsWithin a (.Ioc a b)).Tendsto (fun x ↦ f x / g x) (nhds L) :=
-- proof
  Filter.Tendsto.of_div' hab hf hg hf' hg' hfa hga hgnon hderiv


-- created on 2026-10-22
