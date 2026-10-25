/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/AlderTotient.lean -/


import Def.NumberTheory.ArithmeticFunction.AlderTotient
import Lemma.Nat.ArithmeticFunction.AlderTotient
open ArithmeticFunction


example (k : ℕ) :
    alderTotientTwo k =
      ((Finset.range k).filter fun r =>
        Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card :=
  alderTotientTwo_apply k

example (k : ℕ) :
    alderTotientTwo (k + 1) =
      ((Finset.Iic k).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card :=
  alderTotientTwo_succ_Iic_apply k

example : alderTotientTwo 0 = 0 := by rfl

example : alderTotientTwo 1 = 1 := by rfl

example : alderTotientTwo 5 = 3 := by rfl

example : alderTotientTwo 9 = 3 := by rfl

example (k : ℕ) : alderTotientTwo k ≤ Nat.totient k :=
  alderTotientTwo_le_totient k

example : alderTotientTwo 5 < Nat.totient 5 := by decide

