import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.Mul_Get
open Vector


@[main]
private lemma left
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {a : α}
-- given
  (h : a ≠ 0)
  (b : List.Vector α n) :
-- imply
  a * b / a = b := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [GetDiv.eq.DivGet]
  rw [GetMul.eq.Mul_Get]
  rw [Nat.EqDivMul.of.Ne_0.left h]


@[main]
private lemma main
  [MonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {a : α}
-- given
  (h : a ≠ 0)
  (b : List.Vector α n) :
-- imply
  b * a / a = b := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [GetDiv.eq.DivGet]
  rw [GetMul.eq.MulGet]
  rw [Nat.EqDivMul.of.Ne_0 h]


-- created on 2026-08-16
