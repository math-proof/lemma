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
public import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Computation rule: the forward map takes the identity branch. -/
theorem opcPart2Fwd_pos (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : y % 5 = 2 ∨ y % 5 = 3) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_left hcase

/-- Computation rule: the forward map takes the swap branch. -/
theorem opcPart2Fwd_neg (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(y, x), opc_fwd_mem_y y hny hcase,
        opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
        opc_fwd_eq_swap M x y heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_right hcase

/-- Computation rule: the backward map keeps the coordinates. -/
theorem opcPart2Bwd_pos (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq = ⟨⟨(a, b), heq, h⟩, opc_bwd_hn b hb⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_left h

/-- Computation rule: the backward map swaps the coordinates back. -/
theorem opcPart2Bwd_neg (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq
      = ⟨⟨(b, a), opc_bwd_eq_swap M a b heq, opc_bwd_hba a b ha hb h⟩,
        opc_bwd_hna a ha⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_right h

end MetaMathlibExt
end
