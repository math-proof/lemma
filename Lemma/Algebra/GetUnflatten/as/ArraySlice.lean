import stdlib.SEq
import Lemma.Algebra.ValGetUnflatten.eq.ValArraySlice
import Lemma.Algebra.HEq.of.EqValS
open Algebra


@[main, comm]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m) :
-- imply
  v.unflatten[i] ≃ v.array_slice (i * n) n := by
-- proof
  simp [SEq]
  constructor
  .
    apply Le_SubMulS
  .
    apply HEq.of.EqValS
    apply ValGetUnflatten.eq.ValArraySlice


-- created on 2025-05-31
