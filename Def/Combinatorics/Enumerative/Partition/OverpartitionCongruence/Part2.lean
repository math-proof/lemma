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
public import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

def opcSplitFwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) : {_x : ℤ // True} :=
  match p with
  | .inl (.inl ⟨x, _⟩) => ⟨x, trivial⟩
  | .inl (.inr ⟨x, _⟩) => ⟨x, trivial⟩
  | .inr ⟨x, _⟩ => ⟨x, trivial⟩

def opcSplitBwd (t : {_x : ℤ // True}) :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) :=
  if h0 : t.val % 5 = 0 then .inl (.inl ⟨t.val, h0⟩)
  else if h1 : t.val % 5 = 1 ∨ t.val % 5 = 4 then .inl (.inr ⟨t.val, h1⟩)
  else .inr ⟨t.val, by omega⟩

end MetaMathlibExt
end
