import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.EqPermute
open List


@[main, comm, cast, subst 0]
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
-- updated on 2026-07-19
