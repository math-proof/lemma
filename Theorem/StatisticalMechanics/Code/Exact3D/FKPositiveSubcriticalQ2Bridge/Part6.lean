/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part6
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem PositiveSubexponentialPrefactor.const {c : ℝ} (hc : 0 < c) :
    PositiveSubexponentialPrefactor (fun _ : ℕ => c) := by
  constructor
  · exact Eventually.of_forall fun _ => hc
  · exact tendsto_const_div_atTop_nhds_zero_nat (Real.log c)


theorem PositiveSubexponentialPrefactor.add {A B : ℕ → ℝ}
    (hA : PositiveSubexponentialPrefactor A)
    (hB : PositiveSubexponentialPrefactor B) :
    PositiveSubexponentialPrefactor (fun n => A n + B n) := by
  constructor
  · filter_upwards [hA.1, hB.1] with n hAn hBn
    exact add_pos hAn hBn
  · have hupper :
        Tendsto
          (fun n : ℕ =>
            Real.log 2 / (n : ℝ) +
              max (Real.log (A n) / (n : ℝ))
                (Real.log (B n) / (n : ℝ))) atTop (nhds 0) := by
      have htwo :
          Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
      simpa using htwo.add (hA.2.max hB.2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA.2 hupper ?_ ?_
    · filter_upwards [hA.1, hB.1, Nat.eventually_pos] with n hAn hBn hn
      have hsum_pos : 0 < A n + B n := add_pos hAn hBn
      have hle_sum : A n ≤ A n + B n := by linarith
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hAn hle_sum) (by positivity)
    · filter_upwards [hA.1, hB.1, Nat.eventually_pos] with n hAn hBn hn
      have hsum_pos : 0 < A n + B n := add_pos hAn hBn
      have hmax_pos : 0 < max (A n) (B n) :=
        lt_of_lt_of_le hAn (le_max_left _ _)
      have hsum_le : A n + B n ≤ 2 * max (A n) (B n) := by
        calc
          A n + B n ≤ max (A n) (B n) + max (A n) (B n) :=
            add_le_add (le_max_left _ _) (le_max_right _ _)
          _ = 2 * max (A n) (B n) := by ring
      have hlog_le :
          Real.log (A n + B n) ≤ Real.log (2 * max (A n) (B n)) :=
        Real.log_le_log hsum_pos hsum_le
      have hlog_mul :
          Real.log (2 * max (A n) (B n)) =
            Real.log 2 + Real.log (max (A n) (B n)) := by
        rw [Real.log_mul]
        · norm_num
        · exact ne_of_gt hmax_pos
      have hlog_max :
          Real.log (max (A n) (B n)) =
            max (Real.log (A n)) (Real.log (B n)) := by
        by_cases hAB : A n ≤ B n
        · have hlogAB : Real.log (A n) ≤ Real.log (B n) :=
            Real.log_le_log hAn hAB
          rw [max_eq_right hAB, max_eq_right hlogAB]
        · have hBA : B n ≤ A n := le_of_not_ge hAB
          have hlogBA : Real.log (B n) ≤ Real.log (A n) :=
            Real.log_le_log hBn hBA
          rw [max_eq_left hBA, max_eq_left hlogBA]
      have hlog_le' :
          Real.log (A n + B n) ≤
            Real.log 2 + max (Real.log (A n)) (Real.log (B n)) := by
        simpa [hlog_mul, hlog_max] using hlog_le
      calc
        Real.log (A n + B n) / (n : ℝ) ≤
            (Real.log 2 + max (Real.log (A n)) (Real.log (B n))) /
              (n : ℝ) :=
          div_le_div_of_nonneg_right hlog_le' (by positivity)
        _ = Real.log 2 / (n : ℝ) +
            max (Real.log (A n) / (n : ℝ))
              (Real.log (B n) / (n : ℝ)) := by
          rw [add_div]
          rw [max_div_div_right]
          positivity


theorem PositiveSubexponentialPrefactor.mul {A B : ℕ → ℝ}
    (hA : PositiveSubexponentialPrefactor A)
    (hB : PositiveSubexponentialPrefactor B) :
    PositiveSubexponentialPrefactor (fun n => A n * B n) := by
  constructor
  · filter_upwards [hA.1, hB.1] with n hAn hBn
    exact mul_pos hAn hBn
  · have hsum :
        Tendsto
          (fun n : ℕ =>
            Real.log (A n) / (n : ℝ) +
              Real.log (B n) / (n : ℝ)) atTop (nhds 0) := by
      simpa using hA.2.add hB.2
    refine Tendsto.congr' ?_ hsum
    filter_upwards [hA.1, hB.1] with n hAn hBn
    rw [Real.log_mul hAn.ne' hBn.ne', add_div]


theorem PositiveSubexponentialPrefactor.const_mul {A : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hA : PositiveSubexponentialPrefactor A) :
    PositiveSubexponentialPrefactor (fun n => c * A n) :=
  PositiveSubexponentialPrefactor.mul
    (PositiveSubexponentialPrefactor.const hc) hA


theorem PositiveSubexponentialPrefactor.natCast_pow (k : ℕ) :
    PositiveSubexponentialPrefactor (fun n : ℕ => (n : ℝ) ^ k) := by
  constructor
  · filter_upwards [Nat.eventually_pos] with n hn
    exact pow_pos (by exact_mod_cast hn) k
  · have hlog_div :
        Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
          atTop (nhds 0) := by
      simpa using
        (Real.isLittleO_log_id_atTop.comp_tendsto
          (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero
    have hmul :
        Tendsto (fun n : ℕ =>
          (k : ℝ) * (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
      simpa using hlog_div.const_mul (k : ℝ)
    simpa [Real.log_pow, mul_div_assoc] using hmul


theorem PositiveSubexponentialPrefactor.eventually_le_exp_mul {A : ℕ → ℝ}
    (hA : PositiveSubexponentialPrefactor A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, A n ≤ Real.exp (ε * (n : ℝ)) := by
  have hlt : ∀ᶠ n in atTop, Real.log (A n) / (n : ℝ) < ε := by
    exact hA.2.eventually (Iio_mem_nhds hε)
  filter_upwards [hA.1, hlt, Nat.eventually_pos] with n hApos hlt_n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hlt_n hnpos
  have hlog_lt : Real.log (A n) < ε * (n : ℝ) := by
    simpa [div_mul_cancel₀ _ hnpos.ne'] using hmul
  calc
    A n = Real.exp (Real.log (A n)) := by
      rw [Real.exp_log hApos]
    _ ≤ Real.exp (ε * (n : ℝ)) :=
      Real.exp_le_exp.mpr (le_of_lt hlog_lt)


theorem PositiveSubexponentialPrefactor.congr {A B : ℕ → ℝ}
    (hAB : ∀ᶠ n in atTop, A n = B n)
    (hA : PositiveSubexponentialPrefactor A) :
    PositiveSubexponentialPrefactor B := by
  constructor
  · filter_upwards [hAB, hA.1] with n hABn hAn
    rwa [← hABn]
  · exact Tendsto.congr' (hAB.mono fun _ hABn => by rw [hABn]) hA.2


theorem boxBoundaryCard3_eventually_eq :
    ∀ᶠ n in atTop,
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) =
        24 * (n : ℝ) ^ 2 + 2 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [FK.fup_boundary_card_eq 3 n, Lattice.boxSV_boundary_card 3 n hn]
  have hle : (2 * n - 1) ^ 3 ≤ (2 * n + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hsub : (1 : ℕ) ≤ 2 * n := by omega
  have hsubR : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, hsubR]
  push_cast
  ring_nf


theorem boxBoundaryCard3_eventually_le_26_mul_sq :
    ∀ᶠ n in atTop,
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) ≤
        26 * (n : ℝ) ^ 2 := by
  filter_upwards [boxBoundaryCard3_eventually_eq, eventually_ge_atTop 1]
    with n hcard hn
  rw [hcard]
  have hnR : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hsquare : 1 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  nlinarith


theorem boxBoundaryCard3_positiveSubexponentialPrefactor :
    PositiveSubexponentialPrefactor
      (fun n : ℕ => ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)) := by
  have hpoly : PositiveSubexponentialPrefactor
      (fun n : ℕ => 24 * (n : ℝ) ^ 2 + 2) := by
    exact PositiveSubexponentialPrefactor.add
      (PositiveSubexponentialPrefactor.const_mul
        (by norm_num : (0 : ℝ) < 24)
        (PositiveSubexponentialPrefactor.natCast_pow 2))
      (PositiveSubexponentialPrefactor.const (by norm_num : (0 : ℝ) < 2))
  exact PositiveSubexponentialPrefactor.congr
    (boxBoundaryCard3_eventually_eq.mono fun _ hn => hn.symm) hpoly


theorem boxBoundaryCard3_mul_positiveSubexponentialPrefactor {A : ℕ → ℝ}
    (hA : PositiveSubexponentialPrefactor A) :
    PositiveSubexponentialPrefactor
      (fun n : ℕ =>
        ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * A n) :=
  PositiveSubexponentialPrefactor.mul
    boxBoundaryCard3_positiveSubexponentialPrefactor hA


theorem exists_positiveSubexponentialPrefactor_add
    {A B : ℕ → ℝ}
    (hApos : ∀ᶠ n in atTop, 0 < A n)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hlogA :
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) atTop
        (nhds 0))
    (hlogB :
      Tendsto (fun n : ℕ => Real.log (B n) / (n : ℝ)) atTop
        (nhds 0)) :
    ∃ C : ℕ → ℝ,
      (∀ᶠ n in atTop, 0 < C n) ∧
        Tendsto (fun n : ℕ => Real.log (C n) / (n : ℝ)) atTop
          (nhds 0) ∧
        ∀ᶠ n in atTop, A n + B n ≤ C n := by
  let C : ℕ → ℝ := fun n => A n + B n
  have hC : PositiveSubexponentialPrefactor C :=
    PositiveSubexponentialPrefactor.add ⟨hApos, hlogA⟩ ⟨hBpos, hlogB⟩
  exact ⟨C, hC.1, hC.2, Eventually.of_forall fun _ => le_rfl⟩


end Exact3D
end StatMech
