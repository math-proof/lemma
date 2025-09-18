import Lemma.Logic.Bool.eq.Ite
import Lemma.Algebra.Mul_Ite.eq.Ite_MulS
import Lemma.Logic.Ite_Ite.eq.Ite__Ite
open Logic Algebra


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
