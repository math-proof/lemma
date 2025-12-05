import Lemma.Nat.Ite.eq.AddMulSBool
open Nat


@[main]
private lemma main
  [Decidable p]
  [NonAssocSemiring α]
-- given
  (a : α) :
-- imply
  (if p then
    a
  else
    0) = Bool.toNat p * a := by
-- proof
  simp [Ite.eq.AddMulSBool]


-- created on 2025-12-05
