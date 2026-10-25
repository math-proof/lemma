/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part2


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalLogCoeff_eq_tsum
    (L : ℕ) [NeZero L] (omega u v : ℂ)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalLogCoeff L omega u v m =
      -(∑' r : ℕ,
        (∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L omega u v d
          else 0) / ((r : ℂ) + 1)) / 2 := by
  unfold ons_decFormalLogCoeff
  congr 2
  symm
  apply tsum_eq_sum
  intro r hr
  rw [Finset.mem_range, not_lt] at hr
  have hsum :
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro heq
    have hlen := ons_decLoopExponent_length_le L d
    rw [heq] at hlen
    omega
  rw [hsum, zero_div]

theorem ons_decFormalLog_constantCoeff
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries.constantCoeff
      (ons_decFormalLog L omega u v) = 0 := by
  change ons_decFormalLogCoeff L omega u v 0 = 0
  simp [ons_decFormalLog, ons_decFormalLogCoeff,
    ons_finsuppTotalDegree]

theorem ons_decFormalLog_hasSubst
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    PowerSeries.HasSubst (ons_decFormalLog L omega u v) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalLog_constantCoeff L omega u v)


end StatMech.Onsager
