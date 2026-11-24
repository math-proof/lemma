module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Multiset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Def.Combinatorics.Enumerative.Partition.Overpartition
public import Theorem.Nat.Enumerative.Partition.Overpartition
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Theorem.Real.SpecialFunctions.JacobiTripleProduct
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Def.Analysis.SpecialFunctions.JacobiTripleProduct
public import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

-- Continued: the two-square dissection identity.

/-- In `ZMod 5`, squares equal to `1` come from `±1`. -/
theorem opc_sq_eq_one_iff :
    ∀ a : ZMod 5, a ^ 2 = 1 ↔ a = 1 ∨ a = 4 := by
  decide

/-- In `ZMod 5`, squares equal to `4` come from `±2`. -/
theorem opc_sq_eq_four_iff :
    ∀ a : ZMod 5, a ^ 2 = 4 ↔ a = 2 ∨ a = 3 := by
  decide

/-- Integer residues with square `1` mod 5 are `±1`. -/
theorem opc_mem_pm1 (x : ℤ) (h : ((x : ZMod 5)) ^ 2 = 1) :
    x % 5 = 1 ∨ x % 5 = 4 := by
  have hx : ((x : ZMod 5)) = ((((x % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue x _ rfl
  have h' : ((((x % 5 : ℤ))) : ZMod 5) ^ 2 = 1 := by rw [← hx]; exact h
  have hmem := (opc_sq_eq_one_iff _).mp h'
  rcases hmem with h1 | h4
  · have hd : (5 : ℤ) ∣ x % 5 - 1 := by
      have e : ((((x % 5 - 1 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 1 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 1 := by push_cast; ring
        rw [e1, h1, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ x % 5 - 4 := by
      have e : ((((x % 5 - 4 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 4 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 4 := by push_cast; ring
        rw [e1, h4, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- Integer residues with square `4` mod 5 are `±2`. -/
theorem opc_mem_pm2 (y : ℤ) (h : ((y : ZMod 5)) ^ 2 = 4) :
    y % 5 = 2 ∨ y % 5 = 3 := by
  have hy : ((y : ZMod 5)) = ((((y % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue y _ rfl
  have h' : ((((y % 5 : ℤ))) : ZMod 5) ^ 2 = 4 := by rw [← hy]; exact h
  have hmem := (opc_sq_eq_four_iff _).mp h'
  rcases hmem with h2 | h3
  · have hd : (5 : ℤ) ∣ y % 5 - 2 := by
      have e : ((((y % 5 - 2 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 2 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 2 := by push_cast; ring
        rw [e1, h2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ y % 5 - 3 := by
      have e : ((((y % 5 - 3 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 3 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 3 := by push_cast; ring
        rw [e1, h3, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- A sum of two squares both divisible by 5 is zero mod 5. -/
theorem opc_sq_add_zero_of_zero (x y : ℤ) (hx : x % 5 = 0)
    (hy : y % 5 = 0) : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_zero x hx, opc_sq_zero y hy, add_zero]

/-- A `1 + 4` sum of squares is zero mod 5. -/
theorem opc_sq_add_zero_of_mem (x y : ℤ)
    (hx : x % 5 = 1 ∨ x % 5 = 4) (hy : y % 5 = 2 ∨ y % 5 = 3) :
    ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_one x hx, opc_sq_four y hy]
  decide

/-- The two residue-class conditions cannot hold simultaneously off multiples
of 5: `x ≡ 3y` and `y ≡ 3x` force `5 ∣ y`. -/
theorem opc_no_collide (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5)))
    (hcon : ((y : ZMod 5)) = 3 * ((x : ZMod 5))) : (5 : ℤ) ∣ y := by
  have hy0 : ((y : ZMod 5)) = 0 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    linear_combination 4 * hmod + 3 * hcon
      + ((x : ZMod 5) + (y : ZMod 5) * 2) * h5
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0

end MetaMathlibExt
end
