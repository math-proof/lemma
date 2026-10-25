/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectZeroTurnDualTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega) :
    X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ↔
      ∃ x ∈ (fkRectZeroTurnRemainderDualBoundaryCycleWalk
        R omega C).support,
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R omega))).connectedComponentMk x = X.1 := by
  classical
  simp [fkRectZeroTurnDualTouchedCrossings]


theorem fkRectOpenGraph_dual_le_dual_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega) ≤
      fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R omega)) := by
  apply fkRectOpenGraph_mono R
  intro e he
  rw [fkRectDualConfigurationEquiv_apply] at he ⊢
  by_cases hcut : fkRectDualEdgeToEdge R e ∈ fkRectTorusCutEdges R
  · rw [fkRectForceCutClosed_of_mem R omega _ hcut]
    rfl
  · rwa [fkRectForceCutClosed_of_not_mem R omega _ hcut]


theorem fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hwind : (fkRectWalkWinding R
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C)).1 ≠ 0) :
    (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
  let p := fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C
  let hle := fkRectOpenGraph_dual_le_dual_forceCutClosed R omega
  let q := p.mapLe hle
  have hqwind : (fkRectWalkWinding R q).1 ≠ 0 := by
    simpa only [q, fkRectWalkWinding_mapLe] using hwind
  obtain ⟨X, hcross, z, hz, hcomponent⟩ :=
    exists_fkRectRawHorizontalCrossingComponent_touched_of_winding
      R _ q hqwind
  refine ⟨⟨X, hcross⟩,
    (mem_fkRectZeroTurnDualTouchedCrossings R omega C _).2 ?_⟩
  refine ⟨z, ?_, hcomponent⟩
  simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hz


theorem fkRectZeroTurnDualTouchedCrossings_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
  apply fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding R omega C
  rw [fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding]
  exact fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C


end
end StatMech.FrontierD
