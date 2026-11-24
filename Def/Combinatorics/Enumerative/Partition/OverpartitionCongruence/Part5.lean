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
public import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
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
