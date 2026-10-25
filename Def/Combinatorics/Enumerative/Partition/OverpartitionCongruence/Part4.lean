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
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part3


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

def opcT (M : ℕ) : Type :=
  {t : ℤ × ℤ // t.1 ^ 2 + t.2 ^ 2 = ((((5 * M : ℕ))) : ℤ) ∧
    ((t.1 : ℤ) : ZMod 5) = 3 * ((t.2 : ℤ) : ZMod 5)}

def opcPhi (M : ℕ) :
    opcSq (fun _ => True) (fun _ => True) M ≃ opcT M where
  toFun s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    exact ⟨(u + 2 * v, 2 * u - v), by
      have e : (u + 2 * v) ^ 2 + (2 * u - v) ^ 2 = 5 * (u ^ 2 + v ^ 2) := by
        ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e, h, eM], by
        have e0 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact ⟨v - u, by push_cast; ring⟩
        have e1 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5)
            = ((((u + 2 * v : ℤ))) : ZMod 5)
              - 3 * ((((2 * u - v : ℤ))) : ZMod 5) := by push_cast; ring
        rw [e1] at e0
        exact sub_eq_zero.mp e0⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    refine ⟨((x + 2 * y) / 5, (2 * x - y) / 5), trivial, trivial, ?_⟩
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    have key : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = 25 * ((((M : ℕ))) : ℤ) := by
      have e2 : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
          = (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2 := by
        ring
      have e3 : (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2
          = 5 * (x ^ 2 + y ^ 2) := by rw [hu, hv]; ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e2, e3, heq, eM]
      ring
    have hfin : ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = ((((M : ℕ))) : ℤ) :=
      mul_left_cancel₀ (show (25 : ℤ) ≠ 0 by norm_num) key
    exact hfin
  left_inv s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    apply Subtype.ext
    change ((u + 2 * v + 2 * (2 * u - v)) / 5, (2 * (u + 2 * v) - (2 * u - v)) / 5)
      = (u, v)
    have e1 : u + 2 * v + 2 * (2 * u - v) = 5 * u := by ring
    have e2 : 2 * (u + 2 * v) - (2 * u - v) = 5 * v := by ring
    rw [e1, e2]
    congr 1
    · have hd : (5 : ℤ) ∣ 5 * u := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
    · have hd : (5 : ℤ) ∣ 5 * v := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
  right_inv t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    apply Subtype.ext
    change (((x + 2 * y) / 5 + 2 * ((2 * x - y) / 5)),
        (2 * ((x + 2 * y) / 5) - ((2 * x - y) / 5))) = (x, y)
    congr 1
    · have h5 : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
          = 5 * x := by
        have e : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
            = (5 * ((x + 2 * y) / 5)) + 2 * (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5
    · have h5 : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
          = 5 * y := by
        have e : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
            = 2 * (5 * ((x + 2 * y) / 5)) - (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5

end MetaMathlibExt
end
