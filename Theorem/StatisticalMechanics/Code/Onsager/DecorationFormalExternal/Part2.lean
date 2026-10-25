/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part2


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalAvoidRoot_coeff_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    MvPowerSeries.coeff m (ons_decFormalAvoidRoot L a b d) = 0 := by
  classical
  unfold ons_decFormalAvoidRoot
  rw [PowerSeries.coeff_subst
    (ons_decFormalAvoidLog_hasSubst L a b d)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro g hg
  have hsum := congrArg (fun x : ons_DecEdge L →₀ ℕ ↦
    x s(d, ons_dartRev L d)) (Finset.mem_finsuppAntidiag.mp hg).1
  simp only [Finsupp.finsetSum_apply] at hsum
  have hexists : ∃ i ∈ Finset.range n,
      g i s(d, ons_dartRev L d) ≠ 0 := by
    by_contra hnone
    have hall : ∀ i ∈ Finset.range n,
        g i s(d, ons_dartRev L d) = 0 := by
      intro i hi
      exact not_ne_iff.mp (fun hne ↦ hnone ⟨i, hi, hne⟩)
    have hzero : ∑ i ∈ Finset.range n,
        g i s(d, ons_dartRev L d) = 0 := Finset.sum_eq_zero hall
    rw [hzero] at hsum
    exact hmedge hsum.symm
  obtain ⟨i, hi, hgi⟩ := hexists
  apply Finset.prod_eq_zero hi
  change ons_decFormalAvoidLogCoeff L a b d (g i) = 0
  exact ons_decFormalAvoidLogCoeff_eq_zero_of_external
    L a b d (g i) hgi

end StatMech.Onsager
