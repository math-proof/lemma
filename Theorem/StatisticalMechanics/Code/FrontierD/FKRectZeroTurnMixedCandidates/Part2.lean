/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectZeroTurnPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C ↔
      ∃ x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).support,
        (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x = X.1 := by
  classical
  simp [fkRectZeroTurnPrimalTouchedCrossings]


theorem fkRectZeroTurnPrimalTouchedCrossing_matches
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
    FKRectZeroTurnCrossingMatches R omega C X := by
  obtain ⟨x, hx, hcomponent⟩ :=
    (mem_fkRectZeroTurnPrimalTouchedCrossings R omega C X).1 hX
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  have htorusX : fkRectRawPrimalCrossingTorusComponent R omega X =
      (fkRectOpenGraph R omega).connectedComponentMk x := by
    unfold fkRectRawPrimalCrossingTorusComponent
    rw [← hcomponent]
    exact fkRectRawPrimalCrossingTorusComponent_mk R omega x
  unfold FKRectZeroTurnCrossingMatches
  rw [htorusX,
    fkRectZeroTurnRemainderPrimalComponent_eq_label R omega C]
  apply SimpleGraph.ConnectedComponent.sound
  exact ⟨(p.takeUntil x hx).reverse⟩

theorem fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D := by
  have hC := fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hXC
  have hD := fkRectZeroTurnPrimalTouchedCrossing_matches R omega D X hXD
  exact hC.symm.trans hD


theorem fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (havoid : FKRectWalkAvoidsRowSeam R
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C))) :
    (fkRectZeroTurnPrimalTouchedCrossings R omega C).Nonempty := by
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  obtain ⟨X, hcross, z, hz, hcomponent⟩ :=
    exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk
      R omega p havoid
        (fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C)
  refine ⟨⟨X, hcross⟩,
    (mem_fkRectZeroTurnPrimalTouchedCrossings R omega C _).2 ?_⟩
  exact ⟨z, hz, hcomponent⟩


end
end StatMech.FrontierD
