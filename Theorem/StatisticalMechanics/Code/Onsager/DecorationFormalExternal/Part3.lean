/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part4


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decLoopExponent_external_eq_one_of_firstReturn
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : ons_Dart L) (loop : Fin n → ons_Dart L)
    (hfirst : ons_decIsFirstReturnLoop d loop) :
    ons_decLoopExponent L loop s(d, ons_dartRev L d) = 1 := by
  rw [ons_decLoopExponent_external_apply]
  rw [Fintype.sum_eq_single (0 : Fin n)]
  · rw [if_pos (Or.inl hfirst.1)]
  · intro k hkzero
    rw [if_neg]
    exact not_or_intro (hfirst.2.1 k hkzero) (hfirst.2.2 k)

theorem ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 1) :
    ons_decFormalFirstReturnCoeff L a b d m = 0 := by
  classical
  unfold ons_decFormalFirstReturnCoeff
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro loop hloop
  rw [if_neg]
  rintro ⟨hfirst, hexponent⟩
  apply hmedge
  rw [← hexponent]
  exact ons_decLoopExponent_external_eq_one_of_firstReturn
    L d loop hfirst

theorem ons_decFormalFirstReturn_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalFirstReturn L a b d) = 0 := by
  change ons_decFormalFirstReturnCoeff L a b d 0 = 0
  simp [ons_decFormalFirstReturnCoeff, ons_finsuppTotalDegree]

theorem ons_decFormalFirstReturn_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (ons_decFormalFirstReturn L a b d) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalFirstReturn_constantCoeff L a b d)

end StatMech.Onsager
