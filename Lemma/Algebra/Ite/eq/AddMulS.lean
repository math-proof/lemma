import Lemma.Algebra.Ite.eq.AddMulSBool
import Lemma.Bool.BoolNot.eq.Sub1
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Logic.Bool.le.One
open Algebra Logic Bool


@[main]
private lemma main
  [Decidable p]
  [Ring α]
-- given
  (a b : α) :
-- imply
  (if p then
    a
  else
    b) = Bool.toNat p * a + (1 - Bool.toNat p) * b := by
-- proof
  rw [Ite.eq.AddMulSBool]
  rw [BoolNot.eq.Sub1]
  rw [CoeSub.eq.SubCoeS.of.Ge]
  · 
    aesop
  · 
    apply Bool.le.One


-- created on 2025-07-20
