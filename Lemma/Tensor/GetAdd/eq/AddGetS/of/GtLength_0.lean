import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.Lt_Length.of.GtLength_0
open Tensor


@[main]
private lemma main
  [Add α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (A B : Tensor α s)
  (i : Fin s[0]) :
-- imply
  (A + B).get ⟨i, by apply Lt_Length.of.GtLength_0 h⟩ = A.get ⟨i, by apply Lt_Length.of.GtLength_0 h⟩ + B.get ⟨i, by apply Lt_Length.of.GtLength_0 h⟩ := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    rw [GetAdd.eq.AddGetS.fin]


-- created on 2025-11-06
