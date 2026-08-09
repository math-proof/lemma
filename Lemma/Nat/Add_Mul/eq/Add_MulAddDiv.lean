import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.MulAdd.eq.AddMulS
open Nat


@[main, comm]
private lemma main
  [IntegerRing Z]
-- given
  (a d k : Z) :
-- imply
  a + k * d = a % d + (a / d + k) * d := by
-- proof
  rw [MulAdd.eq.AddMulS]
  rw [Add_Add.eq.AddAdd]
  rw [AddAdd.swap]
  rw [EqAddMulDiv]


-- created on 2026-08-09
