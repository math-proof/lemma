/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.NumberTheory.SelbergSieve
import Lemma.Nat.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals
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
