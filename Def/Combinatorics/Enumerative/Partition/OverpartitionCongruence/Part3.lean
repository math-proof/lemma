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
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part2


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
