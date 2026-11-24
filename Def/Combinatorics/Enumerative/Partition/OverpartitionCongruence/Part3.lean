module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Multiset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Def.Combinatorics.Enumerative.Partition.Overpartition
public import Theorem.Nat.Enumerative.Partition.Overpartition
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Lemma.Real.SpecialFunctions.JacobiTripleProduct
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
public import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

def opcSplit :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) ≃ {_x : ℤ // True} where
  toFun := opcSplitFwd
  invFun := opcSplitBwd
  left_inv := opcSplit_bwd_fwd
  right_inv := opcSplit_fwd_bwd

def opcSq (P Q : ℤ → Prop) (N : ℕ) : Type :=
  {t : ℤ × ℤ // P t.1 ∧ Q t.2 ∧ t.1 ^ 2 + t.2 ^ 2 = (((N : ℕ)) : ℤ)}

def opcFiberSqEquiv (P Q : ℤ → Prop) (N : ℕ) :
    {p : {x : ℤ // P x} × {x : ℤ // Q x} //
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = N} ≃ opcSq P Q N where
  toFun p := by
    obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ := p
    exact ⟨(x, y), hx, hy, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by rw [h]
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq] at h'
      exact h'⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, hx, hy, h⟩ := t
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq]
        exact h
      exact_mod_cast h'⟩
  left_inv p := by obtain ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ := p; rfl
  right_inv t := by obtain ⟨⟨x, y⟩, _, _, _⟩ := t; rfl

end MetaMathlibExt
end
