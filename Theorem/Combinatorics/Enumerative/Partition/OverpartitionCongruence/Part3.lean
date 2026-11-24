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
public import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

theorem opc_sq_zero (x : ℤ) (h : x % 5 = 0) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have hh := opc_intCast_residue x 0 h
    rwa [Int.cast_zero] at hh
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

theorem opc_sq_one (x : ℤ) (h : x % 5 = 1 ∨ x % 5 = 4) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 1 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have hh := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at hh
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

theorem opc_sq_four (x : ℤ) (h : x % 5 = 2 ∨ x % 5 = 3) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 4 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

theorem opc_dvd_add (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ x + 2 * y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((x + 2 * y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((x + 2 * y : ℤ))) : ZMod 5)
        = ((x : ZMod 5)) + 2 * ((y : ZMod 5)) := by push_cast; ring
    have e2 : (3 : ZMod 5) * ((y : ZMod 5)) + 2 * ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

theorem opc_dvd_sub (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ 2 * x - y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((2 * x - y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((2 * x - y : ℤ))) : ZMod 5)
        = 2 * ((x : ZMod 5)) - ((y : ZMod 5)) := by push_cast; ring
    have e2 : 2 * ((3 : ZMod 5) * ((y : ZMod 5))) - ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

end MetaMathlibExt
end
