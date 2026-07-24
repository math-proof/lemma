import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.EqGetStack
import Lemma.Bool.SEq.is.Eq
open Tensor Bool


@[main]
private lemma main
-- given
  (h : n = m)
  (g : List ℕ → List ℕ)
  (f : Tensor α s → Tensor α (g s))
  (X : Tensor α (n :: s)) :
-- imply
  have : X.length = m := by aesop
  [i < n] (f X[i]) ≃ [i < m] (f X[i]) := by
-- proof
  apply SEq.of.All_SEqGetS.Eq.Eq h rfl
  simp_all
  intro i
  simp [GetElem.getElem]
  repeat rw [EqGetStack.fn.fin]
  simp
  apply SEq.of.Eq
  rfl


-- created on 2025-07-13
