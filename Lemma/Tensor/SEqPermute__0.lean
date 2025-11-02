import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.EqPermute__0
open List


@[main, comm]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.permute i 0 ≃ X := by
-- proof
  constructor
  ·
    rw [EqPermute__0]
  ·
    unfold Tensor.permute
    split_ifs <;>
      simp


-- created on 2025-07-14
