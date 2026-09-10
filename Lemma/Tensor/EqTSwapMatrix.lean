import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqGetT
import Lemma.Tensor.GetSwapMatrix.eq.Ite
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
-- given
  (n i₀ j₀ : ℕ) :
-- imply
  (SwapMatrix (α := α) n i₀ j₀)ᵀ = SwapMatrix (α := α) n i₀ j₀ := by
-- proof
  let S := SwapMatrix (α := α) n i₀ j₀
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (EqGetT S j i).trans
  have hi := GetSwapMatrix.eq.Ite (α := α) i₀ j₀ i j
  have hj := GetSwapMatrix.eq.Ite (α := α) i₀ j₀ j i
  simp only [GetElem.getElem] at hi hj ⊢
  erw [hj, hi]
  simp only [Nat.Delta.eq.Ite]
  split_ifs <;> first | rfl | grind


-- created on 2026-09-10
