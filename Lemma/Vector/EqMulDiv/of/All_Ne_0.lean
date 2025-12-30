import Lemma.Rat.EqMulDiv.of.Ne_0
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMul.eq.MulGetS
open Vector Rat


@[main]
private lemma main
  [GroupWithZero α]
  {b : List.Vector α n}
-- given
  (h : ∀ i : Fin n, b[i] ≠ 0)
  (a : List.Vector α n) :
-- imply
  a / b * b = a := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [GetMul.eq.MulGetS]
  rw [GetDiv.eq.DivGetS]
  rw [EqMulDiv.of.Ne_0 (h i)]


@[main]
private lemma fin
  [GroupWithZero α]
  {b : List.Vector α n}
-- given
  (h : ∀ i : Fin n, b.get i ≠ 0)
  (a : List.Vector α n) :
-- imply
  a / b * b = a :=
-- proof
  main h a


-- created on 2025-12-30
