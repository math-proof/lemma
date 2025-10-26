import Lemma.Bool.Bool.eq.Ite
import Lemma.Nat.Mul_Ite.eq.Ite_MulS
import Lemma.Bool.Ite_Ite.eq.Ite__Ite
open Bool Nat


@[main]
private lemma main
  [Decidable p]
  [Decidable q] :
-- imply
  Bool.toNat (p ∧ q) = Bool.toNat p * Bool.toNat q := by
-- proof
  repeat rw [Bool.eq.Ite]
  rw [Mul_Ite.eq.Ite_MulS]
  simp
  rw [Ite_Ite.eq.Ite__Ite]
  aesop


-- created on 2025-07-19
