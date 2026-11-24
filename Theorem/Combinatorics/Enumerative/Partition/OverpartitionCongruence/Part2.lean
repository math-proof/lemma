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
public import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

theorem opcSplit_fwd_bwd (t : {_x : ℤ // True}) :
    opcSplitFwd (opcSplitBwd t) = t := by
  obtain ⟨x, _⟩ := t
  by_cases h0 : x % 5 = 0
  · simp [h0, opcSplitBwd, opcSplitFwd]
  · by_cases h1 : x % 5 = 1 ∨ x % 5 = 4
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]

theorem opcSplit_bwd_fwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) :
    opcSplitBwd (opcSplitFwd p) = p := by
  match p with
  | .inl (.inl ⟨x, h0⟩) => simp [h0, opcSplitBwd, opcSplitFwd]
  | .inl (.inr ⟨x, h1⟩) =>
    have hn0 : ¬ x % 5 = 0 := by omega
    simp [hn0, h1, opcSplitBwd, opcSplitFwd]
  | .inr ⟨x, h2⟩ =>
    have hn0 : ¬ x % 5 = 0 := by omega
    have hn1 : ¬ (x % 5 = 1 ∨ x % 5 = 4) := by omega
    simp [hn0, hn1, opcSplitBwd, opcSplitFwd]

end MetaMathlibExt
end
