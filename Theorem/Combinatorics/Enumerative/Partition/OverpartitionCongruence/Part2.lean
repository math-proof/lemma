/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Lemma.Nat.QuadraticForms.ThreeSquares
import Lemma.Real.SpecialFunctions.JacobiTripleProduct
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Def.Analysis.SpecialFunctions.JacobiTripleProduct
import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part2


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
