import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (s₀ :: s)) :
-- imply
  X = [i < s₀] X[i] := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [← EqGetStack.fn (fun i : Fin s₀ => X[i])]
  rfl


-- created on 2025-07-02
