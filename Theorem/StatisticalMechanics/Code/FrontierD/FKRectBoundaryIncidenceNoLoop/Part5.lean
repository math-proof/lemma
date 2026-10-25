/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part5


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectTorusIndexedEdge R
        (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC).1 ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).edges :=
  (exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
    R omega C hC).choose_spec.2

set_option maxHeartbeats 800000 in


theorem fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (a : R.EdgeIndex)
    (haC : fkRectTorusIndexedEdge R a ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).edges)
    (haD : fkRectTorusIndexedEdge R a ∈
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega D)).edges) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : R.Vertex,
      fkRectTorusIndexedEdge R a = s(x, y) := by
    induction fkRectTorusIndexedEdge R a using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, rfl⟩
  have hxC : x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).support := by
    apply (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).fst_mem_support_of_mem_edges
    rwa [← hxy]
  have hxD : x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega D)).support := by
    apply (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega D)).fst_mem_support_of_mem_edges
    rwa [← hxy]
  rw [fkRectZeroTurnRemainderPrimalComponent_eq_label,
    fkRectZeroTurnRemainderPrimalComponent_eq_label]
  apply SimpleGraph.ConnectedComponent.sound
  exact ((fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C)).takeUntil x hxC).reachable
    |>.trans
      ((fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega D)).takeUntil x hxD).reachable.symm


end
end StatMech.FrontierD
