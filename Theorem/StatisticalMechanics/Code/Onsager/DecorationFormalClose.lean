/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSquarefree
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalAssembly
import Theorem.StatisticalMechanics.Code.Onsager.FinalAssembly
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalClose


namespace StatMech.Onsager

theorem ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes) :
    ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L := by
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes
    L (hvanish L hL)

theorem ons_spinKacWardIdentities_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_decoratedFormal
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes hvanish

theorem ons_free_energy_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) := by
  apply ons_free_energy_of_spinKacWard_all
    (fun gamma ↦ ons_spinKacWardIdentities_of_repeatedEdgeVanishes
      hvanish gamma)
  exact hbeta

end StatMech.Onsager
