import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqMulDiv.of.All_Ne_0
open Tensor Vector


@[main]
private lemma main
  [GroupWithZero α]
  {B : Tensor α s}
-- given
  (h : ∀ i : Fin s.prod, B.data[i] ≠ 0)
  (A : Tensor α s) :
-- imply
  A / B * B = A := by
-- proof
  apply Eq.of.EqDataS
  apply EqMulDiv.of.All_Ne_0 h


@[main]
private lemma fin
  [GroupWithZero α]
  {B : Tensor α s}
-- given
  (h : ∀ i : Fin s.prod, B.data.get i ≠ 0)
  (A : Tensor α s) :
-- imply
  A / B * B = A :=
-- proof
  main h A


-- created on 2025-12-30
