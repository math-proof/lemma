/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/WilsonQuotient.lean -/

import Def.NumberTheory.WilsonQuotient
import Lemma.Int.WilsonQuotient


example : Int.wilsonQuotient 3 = 1 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : Int.wilsonQuotient 5 = 5 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : Int.wilsonQuotient 7 = 103 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : (5 : ℤ) * Int.wilsonQuotient 5 = (Nat.factorial (5 - 1) : ℤ) + 1 :=
  Int.mul_wilsonQuotient 5 (by decide)

example : (Nat.factorial (5 - 1) : ℤ) = (5 : ℤ) * Int.wilsonQuotient 5 - 1 :=
  Int.factorial_eq_mul_wilsonQuotient_sub_one 5 (by decide)

