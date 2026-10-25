/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/WardGeneralizedBinomial.lean -/


import Mathlib.Tactic.NormNum
import Def.Combinatorics.Enumerative.WardGeneralizedBinomial
import Lemma.Finset.Enumerative.WardGeneralizedBinomial


namespace MetaMathlibExt

example : wardUnitsCarry 2 1 1 = 1 := by decide

example : wardUnitsCarry 2 2 1 = 0 := by decide

example : wardUnitsCarry 1 4 7 = 0 := by decide

example : wardGeneralizedBinomialCoefficient (R := ℕ) (fun b => b) 1 1 = 2 := by
  decide

example : wardGeneralizedBinomialCoefficient (R := ℕ) (fun b => b) 2 1 = 3 := by
  decide

example (n m : ℕ) : wardUnitsCarry 0 n m = 0 := by
  rw [wardUnitsCarry_eq_div, Nat.div_zero]

example (n m : ℕ) : wardUnitsCarry 1 n m = 0 := by
  simp [wardUnitsCarry_eq_div, Nat.mod_one]

example (b n m : ℕ) (h : n % b + m % b < b) : wardUnitsCarry b n m = 0 := by
  rw [wardUnitsCarry_eq_div, Nat.div_eq_of_lt h]

example {R : Type*} [CommMonoid R] (s : ℕ → R) : wardGeneralizedBinomialCoefficient s 1 0 = 1 := by
  simp [wardGeneralizedBinomialCoefficient_eq_prod_Icc]

example {R : Type*} [CommMonoid R] (s : ℕ → R) (n m : ℕ) :
    wardGeneralizedBinomialCoefficient s n m =
      ∏ b ∈ Finset.Icc 2 (n + m), s b ^ wardUnitsCarry b n m := by
  simp only [wardGeneralizedBinomialCoefficient_eq_prod_Icc, wardUnitsCarry_eq_div]

example : wardGeneralizedBinomialCoefficient (R := ℕ) (fun b => b) 2 2 = 12 := by
  rw [wardGeneralizedBinomialCoefficient_eq_prod_Icc]
  decide

end MetaMathlibExt
