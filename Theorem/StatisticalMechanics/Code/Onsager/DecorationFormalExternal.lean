/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalExternal


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalLogCoeff_eq_rooted_add_avoid
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) m =
      ons_decFormalRootedLogCoeff L a b d m +
        ons_decFormalAvoidLogCoeff L a b d m := by
  unfold ons_decFormalLogCoeff ons_decFormalRootedLogCoeff
    ons_decFormalAvoidLogCoeff
  have hsum :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ loop : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / ((r : ℂ) + 1)) =
        2 * (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
          ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1)) +
          ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
            ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1) := by
    calc
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ loop : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / ((r : ℂ) + 1)) =
          ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
            (2 * ons_decFormalFixedBucketE L a b d r m +
              ons_decFormalFixedBucketN L a b d r m) / ((r : ℂ) + 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [ons_decLoopScalar_sum_fixedExponent_two_bucket]
      _ = _ := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib]
        have hE :
            (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
              2 * ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1)) =
              2 * ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
                ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        rw [hE]
  rw [hsum]
  ring

theorem ons_decFormalLog_eq_rooted_add_avoid
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalLog L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_decFormalRootedLog L a b d + ons_decFormalAvoidLog L a b d := by
  ext m
  exact ons_decFormalLogCoeff_eq_rooted_add_avoid L a b d m

theorem ons_decFormalFixedBucketN_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (r : ℕ) (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    ons_decFormalFixedBucketN L a b d r m = 0 := by
  classical
  unfold ons_decFormalFixedBucketN
  apply Finset.sum_eq_zero
  intro loop hloop
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop
  push Not at hloop
  rw [if_neg]
  intro hexponent
  apply hmedge
  rw [← hexponent, ons_decLoopExponent_external_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  exact not_or_intro (hloop.1 k) (hloop.2 k)

theorem ons_decFormalAvoidLogCoeff_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    ons_decFormalAvoidLogCoeff L a b d m = 0 := by
  unfold ons_decFormalAvoidLogCoeff
  have hsum :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [ons_decFormalFixedBucketN_eq_zero_of_external
      L a b d r m hmedge, zero_div]
  rw [hsum]
  ring

theorem ons_decFormalAvoidLog_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalAvoidLog L a b d) = 0 := by
  change ons_decFormalAvoidLogCoeff L a b d 0 = 0
  simp [ons_decFormalAvoidLogCoeff, ons_finsuppTotalDegree]

theorem ons_decFormalAvoidLog_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (ons_decFormalAvoidLog L a b d) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalAvoidLog_constantCoeff L a b d)

end StatMech.Onsager
