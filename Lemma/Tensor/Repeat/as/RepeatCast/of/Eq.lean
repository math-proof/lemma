import sympy.tensor.Basic
import stdlib.SEq
import Lemma.Tensor.Repeat.as.RepeatCast.of.Lt_Length.Eq
open Tensor


@[main, comm 1]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  X.repeat n d ≃ (cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simp [← h]⟩ := by
-- proof
  apply Repeat.as.RepeatCast.of.Lt_Length.Eq h


-- created on 2025-10-10
