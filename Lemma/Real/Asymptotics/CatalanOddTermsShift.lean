import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Asymptotics.CatalanOddTermsShift
open scoped BigOperators
open MetaMathlibExt


/--
[catalan_odd_terms_shift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/CatalanOddTermsShift.lean)
-/
@[path]
private lemma catalan_odd_terms_shift_unique_eq
  :
-- imply
  ∀ α : ℝ,
    (∃ a : ℕ → ℝ,
    (∀ N : ℕ,
    Filter.Tendsto
    (fun n : ℕ =>
    ((n : ℝ) + α) ^ N *
    (((Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) *
    Real.sqrt Real.pi *
    Real.rpow ((n : ℝ) + α) ((3 : ℝ) / 2) /
    (4 : ℝ) ^ n) -
    ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + α) ^ k))
    Filter.atTop (nhds 0)) ∧
    (∀ k : ℕ, a (2 * k + 1) = 0)) ↔
    α = (3 : ℝ) / 4 := by
-- proof
  apply MetaMathlibExt.catalan_odd_terms_shift_unique


-- created on 2026-10-20
