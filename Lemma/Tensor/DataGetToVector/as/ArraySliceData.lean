import Lemma.Vector.HEq.of.EqValS
import Lemma.Tensor.ValDataGetToVector.eq.ValArraySliceData
import Lemma.Nat.Le_SubMulS
open Tensor Vector Nat


@[main]
private lemma main
-- given
  (X : Tensor α (s₀ :: s))
  (i : Fin s₀) :
-- imply
  X.toVector[i].data ≃ X.data.array_slice (i * s.prod) s.prod := by
-- proof
  constructor
  .
    simp_all
    apply Le_SubMulS
  .
    apply HEq.of.EqValS
    apply ValDataGetToVector.eq.ValArraySliceData


-- created on 2025-05-23
-- updated on 2025-06-29
