import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DiophantineApproximation.WeylCriterion
open scoped BigOperators
open Filter Topology
open MetaMathlibExt


/--
[weyl_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean)
-/
@[path]
private lemma weyl_criterion_eq
  {x : ℕ → ℝ} :
-- imply
  (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
    ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
    (Finset.range N)).card : ℝ) / (N : ℝ))
    atTop (nhds (b - a)))
    ↔ ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ =>
    (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
    Complex.exp (((2 * Real.pi * (h : ℝ) * x n : ℝ) : ℂ) * Complex.I))
    atTop (nhds 0) := by
-- proof
  apply MetaMathlibExt.weyl_criterion x


-- created on 2026-10-20
