import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetSwapMatrix.eq.Ite
import Lemma.Tensor.GetEye.eq.Delta
open Nat Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (n : ℕ) (i : Fin n) :
-- imply
  SwapMatrix (α := α) n i i = eye n := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro a
  apply Eq.of.All_EqGetS.fin
  intro b
  have hW := GetSwapMatrix.eq.Ite (α := α) i i a b
  have hI := (GetEye.eq.Delta.fin (α := α) a b).symm
  refine (hW.trans ?_).trans hI
  by_cases ha : (a : ℕ) = i
  ·
    simp [ha, Delta.eq.Ite]
    have : a = i := Fin.ext ha
    subst this
    simp [Fin.ext_iff, eq_comm]
    rfl
  ·
    simp [ha, Delta.eq.Ite, eq_comm]
    rfl


-- created on 2026-09-10
