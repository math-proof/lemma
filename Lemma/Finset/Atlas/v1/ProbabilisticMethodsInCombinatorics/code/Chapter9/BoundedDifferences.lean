import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.BoundedDifferences
open BoundedDifferences
open MeasureTheory ProbabilityTheory Real Finset Function
open scoped NNReal ENNReal


/--
[liftToNat_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/BoundedDifferences.lean)
-/
@[path]
lemma liftToNat_nonneg
  {n : ℕ}
  {c : Fin n → ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i) :
-- imply
  ∀ i, 0 ≤ liftToNat c i := by
-- proof
  intro i; simp only [liftToNat]; split_ifs with h
  · exact hc ⟨i, h⟩
  · linarith

/--
[sum_hoeffdingParam_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/BoundedDifferences.lean)
-/
@[path]
lemma sum_hoeffdingParam_eq
  {n : ℕ}
  {c : Fin n → ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i) :
-- imply
  (↑(∑ i < n, hoeffdingParam (liftToNat c i) (liftToNat_nonneg hc i)) : ℝ) = (∑ i : Fin n, c i ^ 2) / 4 := by
-- proof
  rw [NNReal.coe_sum]
  simp only [hoeffdingParam, Nat.Iio_eq_range]
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  congr 1; ext ⟨i, hi⟩
  simp only [liftToNat, hi]
  rfl
-- The Doob martingale construction for a bounded-differences function: given independent
-- `X_i` and `f` with bounded differences `c_i`, the martingale differences `Y_i` satisfy
-- `∑ i, Y_i = f(X) - 𝔼[f(X)]` and each `Y_{i+1}` is conditionally sub-Gaussian
-- with parameter `c_{i+1}^2/4` given `ℱ_i`.


-- created on 2026-10-23
-- updated on 2026-11-26
