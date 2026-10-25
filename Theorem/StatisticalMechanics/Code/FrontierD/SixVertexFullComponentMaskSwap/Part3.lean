/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexFullDisagreementMask.vertexMask_bondMate
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexFullDisagreementVertexMask mask d.1 =
      sixVertexFullDisagreementVertexMask mask
        (sixVertexTorusDartBondMate T d).1 := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  have hlocal : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hforward (hactive : vertexMask d.1 = true) :
      vertexMask (sixVertexTorusDartBondMate T d).1 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).1 hactive
    have hd := hmask.2 d.1 side d.2 hside hlocal
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask _).2
    exact ⟨(sixVertexTorusDartBondMate T d).2, by
      rw [sixVertexTorusLocalSwitchMask_bondMate mask d]
      exact hd⟩
  have hreverse
      (hactive : vertexMask (sixVertexTorusDartBondMate T d).1 = true) :
      vertexMask d.1 = true := by
    let mate := sixVertexTorusDartBondMate T d
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask mate.1).1 hactive
    have hlocalMate : sixVertexLocalIncomingPattern omega mate.1 mate.2 ≠
        sixVertexLocalIncomingPattern eta mate.1 mate.2 := by
      rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      change sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusDartEdge T (sixVertexTorusDartBondMate T d))
      rw [sixVertexTorusDartEdge_bondMate]
      exact hdisagrees
    have hm := hmask.2 mate.1 side mate.2 hside hlocalMate
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).2
    exact ⟨d.2, by
      rw [← sixVertexTorusLocalSwitchMask_bondMate mask d]
      exact hm⟩
  change vertexMask d.1 =
    vertexMask (sixVertexTorusDartBondMate T d).1
  cases hfirst : vertexMask d.1 <;>
    cases hsecond : vertexMask (sixVertexTorusDartBondMate T d).1
  · rfl
  · exact False.elim (by simpa [hfirst] using hreverse hsecond)
  · exact False.elim (by simpa [hsecond] using hforward hfirst)
  · rfl

theorem SixVertexFullDisagreementMask.vertexMask_eq_localMask_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexFullDisagreementVertexMask mask d.1 =
      sixVertexTorusLocalSwitchMask mask d.1 d.2 := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  have hlocal : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hselectedToActive
      (hselected : sixVertexTorusLocalSwitchMask mask d.1 d.2 = true) :
      vertexMask d.1 = true :=
    (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).2
      ⟨d.2, hselected⟩
  have hactiveToSelected (hactive : vertexMask d.1 = true) :
      sixVertexTorusLocalSwitchMask mask d.1 d.2 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).1 hactive
    exact hmask.2 d.1 side d.2 hside hlocal
  change vertexMask d.1 = sixVertexTorusLocalSwitchMask mask d.1 d.2
  cases hvertex : vertexMask d.1 <;>
    cases hedge : sixVertexTorusLocalSwitchMask mask d.1 d.2
  · rfl
  · exact False.elim (by simpa [hvertex] using hselectedToActive hedge)
  · exact False.elim (by simpa [hedge] using hactiveToSelected hvertex)
  · rfl

theorem SixVertexFullDisagreementMask.fullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredFullSwapBondCoherent source
      (sixVertexFullDisagreementVertexMask mask) := by
  intro d hd
  apply (fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq source d).2
  by_contra hedge
  have hdisagrees : sixVertexTorusEdgeDisagrees
      (source false).arrows (source true).arrows
      (sixVertexTorusDartEdge T
        (sixVertexTorusDartOfMedialDart d)) := hedge
  have heq := hmask.vertexMask_bondMate
    (sixVertexTorusDartOfMedialDart d) hdisagrees
  rw [← sixVertexTorusDartOfMedialDart_bondMate] at heq
  exact hd heq


end
end StatMech.FrontierD
