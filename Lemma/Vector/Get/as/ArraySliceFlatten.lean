import stdlib.SEq
import Lemma.Vector.ValGet.eq.ValArraySliceFlatten
import Lemma.Vector.HEq.of.Val
import Lemma.Nat.Le_SubMulS
open Vector Nat


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  v[i] ≃ v.flatten.array_slice (i * n) n := by
-- proof
  simp [SEq]
  constructor
  .
    apply Le_SubMulS
  .
    apply HEq.of.Val
    apply ValGet.eq.ValArraySliceFlatten


-- created on 2025-05-31
