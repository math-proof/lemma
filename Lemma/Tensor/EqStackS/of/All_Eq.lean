import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma fin
  {n : ℕ}
  {f g : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, f i = g i) :
-- imply
  [i < n] f i = [i < n] g i := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  simp [GetElem.getElem]
  repeat rw [EqGetStack.fin.fin]
  apply h i


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → Tensor α s}
-- given
  (h : ∀ i : Fin n, f i = g i) :
-- imply
  [i < n] f i = [i < n] g i :=
-- proof
  fin h


-- created on 2025-06-01
-- updated on 2025-06-14
