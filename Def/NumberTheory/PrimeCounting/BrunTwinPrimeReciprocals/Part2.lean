/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Def.NumberTheory.SelbergSieve
public import Theorem.Nat.SelbergSieve
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals

@[expose] public section

/-!
# Brun's theorem on twin-prime reciprocals

This file records the convergence of the reciprocal series over twin-prime pairs.
-/


section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open MathlibExt.SelbergSieve

def brunPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.range (Y ^ 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

def brunP (Y : ℕ) : ℕ := ∏ p ∈ brunPrimes Y, p

noncomputable def brunF : ℕ →* ℝ where
  toFun n := if Odd n then (2 ^ ArithmeticFunction.cardFactors n : ℝ) / (n : ℝ) else 0
  map_one' := by simp
  map_mul' := by
    intro m n
    change (if Odd (m * n) then
      (2 ^ ArithmeticFunction.cardFactors (m * n) : ℝ) / ((m * n : ℕ) : ℝ)
      else 0) =
      (if Odd m then (2 ^ ArithmeticFunction.cardFactors m : ℝ) / (m : ℝ)
        else 0) *
      (if Odd n then (2 ^ ArithmeticFunction.cardFactors n : ℝ) / (n : ℝ)
        else 0)
    by_cases hm : Odd m
    · by_cases hn : Odd n
      · have hm0 : m ≠ 0 := by
          rintro rfl
          exact Nat.not_odd_zero hm
        have hn0 : n ≠ 0 := by
          rintro rfl
          exact Nat.not_odd_zero hn
        have hmn : Odd (m * n) := (Nat.odd_mul).mpr ⟨hm, hn⟩
        have hcard := ArithmeticFunction.cardFactors_mul hm0 hn0
        rw [ite_eq_left hmn, ite_eq_left hm, ite_eq_left hn, hcard, pow_add]
        push_cast
        field_simp
      · have hmn : ¬ Odd (m * n) := by
          rw [Nat.odd_mul]
          exact fun h => hn h.2
        rw [ite_eq_right hmn, ite_eq_right hn, mul_zero]
    · have hmn : ¬ Odd (m * n) := by
        rw [Nat.odd_mul]
        exact fun h => hm h.1
      rw [ite_eq_right hmn, ite_eq_right hm, zero_mul]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted
end
