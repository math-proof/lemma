import Mathlib
import Lemma.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_ridout_weighted_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
  {k : RothMvIndex m}
-- given
  (hk : ∀ h, k h ≤ r h)
  (μ ν : ℝ) :
-- imply
  μ * rothMvWeight r k + ν * rothMvWeight r (rothRidoutComplement r k) =
    ∑ h, (μ * (k h : ℝ) / r h + ν * ((r h - k h : ℕ) : ℝ) / r h) := by
-- proof
  unfold rothMvWeight
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [RothRidoutComplement.eq.Sub.of.RothMvIndex, Nat.cast_sub (hk h)]
  ring


-- created on 2026-10-21
