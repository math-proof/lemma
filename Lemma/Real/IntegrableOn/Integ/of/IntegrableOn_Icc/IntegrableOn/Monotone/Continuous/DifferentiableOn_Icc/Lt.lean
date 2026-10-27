import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_10
open Chapter11.BoundedInterval Chapter9 Chapter10
open Chapter11


/--
[integ_of_comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_10.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {φ f: ℝ → ℝ}
-- given
  (hab: a < b)
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ)
  (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
-- imply
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
    integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
      integ f (Icc (φ a) (φ b)) :=
-- proof
  Chapter11.integ_of_comp hab hφ_diff hφ_cont hφ_mono hφ' hf


-- created on 2026-10-22
