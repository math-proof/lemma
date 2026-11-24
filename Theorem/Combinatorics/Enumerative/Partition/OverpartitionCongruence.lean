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
public import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

theorem opc_intCast_residue (x r : ℤ) (h : x % 5 = r) :
    ((x : ℤ) : ZMod 5) = ((r : ℤ) : ZMod 5) := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hxx : x = 5 * (x / 5) + r := by omega
  rw [hxx]
  push_cast
  rw [h5, zero_mul, zero_add]

theorem opc_supportA : opcSupportedMod ℤ 5 0 opcA := by
  apply opc_support_thetaOn
  intro x h0
  have h0' : x % 5 = 0 := h0
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have h := opc_intCast_residue x 0 h0'
    rwa [Int.cast_zero] at h
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

theorem opc_supportB : opcSupportedMod ℤ 5 1 opcB := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 1 ∨ x % 5 = 4 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have h := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at h
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

theorem opc_supportC : opcSupportedMod ℤ 5 4 opcC := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 2 ∨ x % 5 = 3 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

end MetaMathlibExt
end
