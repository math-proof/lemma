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
import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part8


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- `a² + b * c` is the 5-expansion of `θ²`. -/
theorem opc_dissection_sq_add_mul_eq_expand :
    opcA ^ 2 + opcB * opcC
      = PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (opcTheta ^ 2) := by
  apply PowerSeries.ext
  intro N
  have hLHS : PowerSeries.coeff N (opcA ^ 2 + opcB * opcC)
      = ((Nat.card (opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) N) : ℕ) : ℤ)
        + ((Nat.card (opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
            (fun x => x % 5 = 2 ∨ x % 5 = 3) N) : ℕ) : ℤ) := by
    unfold opcA opcB opcC
    rw [map_add, pow_two, opc_coeff_mul_thetaOn, opc_coeff_mul_thetaOn]
  rw [hLHS]
  by_cases hd : (5 : ℕ) ∣ N
  · obtain ⟨M, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    have hRHS : PowerSeries.coeff M (opcTheta ^ 2)
        = ((Nat.card (opcSq (fun _ => True) (fun _ => True) M) : ℕ) : ℤ) := by
      unfold opcTheta
      rw [pow_two, opc_coeff_mul_thetaOn]
    rw [hRHS, Nat.card_congr (opcPhi M), opc_card_split M, Nat.cast_add]
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_zero x y hx hy) hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_mem x y hx hy) hd]
    simp

/-- The 5-dissection of `θ⁴`. -/
theorem opc_theta_pow_four_decomp :
    ∃ W R₁ R₂ R₃ R₄ : ℤ⟦X⟧,
      opcSupportedMod ℤ 5 1 R₁ ∧ opcSupportedMod ℤ 5 2 R₂ ∧
        opcSupportedMod ℤ 5 3 R₃ ∧ opcSupportedMod ℤ 5 4 R₄ ∧
        opcTheta ^ 4 = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4)
          + 5 • W + (R₁ + R₂ + R₃ + R₄) := by
  have mAA : opcSupportedMod ℤ 5 0 (opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ opc_supportA opc_supportA
  have mAAA : opcSupportedMod ℤ 5 0 (opcA * opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ mAA opc_supportA
  have mAAAB : opcSupportedMod ℤ 5 1 (opcA * opcA * opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ mAAA opc_supportB
  have mBB : opcSupportedMod ℤ 5 2 (opcB * opcB) :=
    opc_supportedMod_mul 5 1 1 _ _ opc_supportB opc_supportB
  have mABB : opcSupportedMod ℤ 5 2 (opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mBB
  have mABBC : opcSupportedMod ℤ 5 1 (opcA * (opcB * opcB) * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mABB opc_supportC
  have mCC : opcSupportedMod ℤ 5 3 (opcC * opcC) :=
    opc_supportedMod_mul 5 4 4 _ _ opc_supportC opc_supportC
  have mCCC : opcSupportedMod ℤ 5 2 (opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mCC opc_supportC
  have mCCCC : opcSupportedMod ℤ 5 1 (opcC * opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mCCC opc_supportC
  have mBBB : opcSupportedMod ℤ 5 3 (opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 2 1 _ _ mBB opc_supportB
  have mAABB : opcSupportedMod ℤ 5 2 (opcA * opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ mAA mBB
  have mBBBC : opcSupportedMod ℤ 5 2 (opcB * opcB * opcB * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mBBB opc_supportC
  have mACCC : opcSupportedMod ℤ 5 2 (opcA * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mCCC
  have mACC : opcSupportedMod ℤ 5 3 (opcA * opcA * (opcC * opcC)) :=
    opc_supportedMod_mul 5 0 3 _ _ mAA mCC
  have mBCCC : opcSupportedMod ℤ 5 3 (opcB * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 1 2 _ _ opc_supportB mCCC
  have mABBB : opcSupportedMod ℤ 5 3 (opcA * (opcB * opcB * opcB)) :=
    opc_supportedMod_mul 5 0 3 _ _ opc_supportA mBBB
  have mAAAC : opcSupportedMod ℤ 5 4 (opcA * opcA * opcA * opcC) :=
    opc_supportedMod_mul 5 0 4 _ _ mAAA opc_supportC
  have mAB : opcSupportedMod ℤ 5 1 (opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ opc_supportA opc_supportB
  have mABCC : opcSupportedMod ℤ 5 4 (opcA * opcB * (opcC * opcC)) :=
    opc_supportedMod_mul 5 1 3 _ _ mAB mCC
  have mBBBB : opcSupportedMod ℤ 5 4 (opcB * opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 3 1 _ _ mBBB opc_supportB
  refine ⟨2 • (opcA * opcA * opcB * opcC) + opcB * opcB * (opcC * opcC),
    4 • (opcA * opcA * opcA * opcB) + 12 • (opcA * (opcB * opcB) * opcC)
      + opcC * opcC * opcC * opcC,
    6 • (opcA * opcA * (opcB * opcB)) + 4 • (opcB * opcB * opcB * opcC)
      + 4 • (opcA * (opcC * opcC * opcC)),
    6 • (opcA * opcA * (opcC * opcC)) + 4 • (opcB * (opcC * opcC * opcC))
      + 4 • (opcA * (opcB * opcB * opcB)),
    4 • (opcA * opcA * opcA * opcC) + 12 • (opcA * opcB * (opcC * opcC))
      + opcB * opcB * opcB * opcB,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 1 _ 4 mAAAB
      · exact opc_supportedMod_nsmul 5 1 _ 12 mABBC
    · exact mCCCC
  · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 2 _ 6 mAABB
      · exact opc_supportedMod_nsmul 5 2 _ 4 mBBBC
    · exact opc_supportedMod_nsmul 5 2 _ 4 mACCC
  · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 3 _ 6 mACC
      · exact opc_supportedMod_nsmul 5 3 _ 4 mBCCC
    · exact opc_supportedMod_nsmul 5 3 _ 4 mABBB
  · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 4 _ 4 mAAAC
      · exact opc_supportedMod_nsmul 5 4 _ 12 mABCC
    · exact mBBBB
  · have hpow : ((opcTheta ^ 2) ^ 2 : ℤ⟦X⟧) = opcTheta ^ 4 := by ring
    have hsq : (opcA ^ 2 + opcB * opcC) ^ 2
        = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4) := by
      rw [opc_dissection_sq_add_mul_eq_expand, ← map_pow, hpow]
    conv_lhs => rw [opc_theta_eq_dissection]
    rw [← hsq]
    ring

end MetaMathlibExt
end
