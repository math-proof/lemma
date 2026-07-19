import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.EqPermute
open List


@[main, comm, cast]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.permute i 0 ≃ X := by
-- proof
  constructor
  ·
    rw [EqPermute]
  ·
    unfold Tensor.permute
    split_ifs <;>
      simp


-- created on 2025-07-14
