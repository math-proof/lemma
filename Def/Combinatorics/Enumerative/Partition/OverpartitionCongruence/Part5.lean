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
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part4


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- The part of `opcT M` with `5 ∣ y` is the support of `a²`. -/
def opcPart1 (M : ℕ) :
    {t : opcT M // (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) (5 * M) where
  toFun t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hdiv⟩ := t
    have hdiv' : (5 : ℤ) ∣ y := hdiv
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv'
    have hx0 : ((x : ZMod 5)) = 0 := by rw [hmod, hy0, mul_zero]
    have hxdvd : (5 : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    exact ⟨(x, y), (by omega : x % 5 = 0), (by omega : y % 5 = 0), heq⟩
  invFun s := by
    obtain ⟨⟨x, y⟩, hx, hy, heq⟩ := s
    have hxdvd : (5 : ℤ) ∣ x := by omega
    have hydvd : (5 : ℤ) ∣ y := by omega
    have hx0 : ((x : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hxdvd
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hydvd
    exact ⟨⟨(x, y), heq, by rw [hx0, hy0, mul_zero]⟩, hydvd⟩
  left_inv t := by obtain ⟨⟨⟨x, y⟩, _, _⟩, _⟩ := t; rfl
  right_inv s := by obtain ⟨⟨x, y⟩, _, _, _⟩ := s; rfl

end MetaMathlibExt
end
