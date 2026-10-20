import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.WeightedLargeSieve
open scoped BigOperators ComplexConjugate
open MathlibExt.NumberTheory.PrimeCounting


/--
[weightedLargeSieve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/WeightedLargeSieve.lean)
-/
@[path]
private lemma weightedLargeSieve_eq
  [Fintype ι]
  {N : ℕ}
  {x δ : ι → ℝ}
  {a : ℕ → ℂ}
-- given
  (hδ : ∀ r, 0 < δ r)
  (hsep : ∀ r s, r ≠ s → δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
-- imply
  ∑ r, (N + 3 / (2 * δ r))⁻¹ *
    ‖∑ n ∈ Finset.range N, a n *
    Complex.exp (((2 * Real.pi * (n * x r) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
    ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.weightedLargeSieve N x δ a hδ hsep


-- created on 2026-10-20
