/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLexDisagreementComponentVertexMask_bondMate
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 =
      sixVertexLexDisagreementComponentVertexMask T omega eta h
        (sixVertexTorusDartBondMate T d).1 := by
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  have hlocalDisagrees : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hforward (hselected : vertexMask d.1 = true) :
      vertexMask (sixVertexTorusDartBondMate T d).1 = true := by
    have hactive : ∃ side,
        sixVertexTorusLocalSwitchMask edgeMask d.1 side = true :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).1
        hselected
    obtain ⟨side, hside⟩ := hactive
    have hdSelected : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true :=
      sixVertexLexDisagreementComponentMask_incident_closure
        T omega eta h d.1 side d.2 hside hlocalDisagrees
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask _).2
    exact ⟨(sixVertexTorusDartBondMate T d).2, by
      rw [sixVertexTorusLocalSwitchMask_bondMate edgeMask d]
      exact hdSelected⟩
  have hreverse
      (hselected : vertexMask (sixVertexTorusDartBondMate T d).1 = true) :
      vertexMask d.1 = true := by
    let mate := sixVertexTorusDartBondMate T d
    have hedgeMate : sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusDartEdge T mate) := by
      rw [sixVertexTorusDartEdge_bondMate]
      exact hdisagrees
    have hlocalMate : sixVertexLocalIncomingPattern omega mate.1 mate.2 ≠
        sixVertexLocalIncomingPattern eta mate.1 mate.2 :=
      (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
        omega eta mate.1 mate.2).2 hedgeMate
    have hactive : ∃ side,
        sixVertexTorusLocalSwitchMask edgeMask mate.1 side = true :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask mate.1).1
        hselected
    obtain ⟨side, hside⟩ := hactive
    have hmateSelected :
        sixVertexTorusLocalSwitchMask edgeMask mate.1 mate.2 = true :=
      sixVertexLexDisagreementComponentMask_incident_closure
        T omega eta h mate.1 side mate.2 hside hlocalMate
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).2
    refine ⟨d.2, ?_⟩
    rw [← sixVertexTorusLocalSwitchMask_bondMate edgeMask d]
    exact hmateSelected
  change vertexMask d.1 = vertexMask (sixVertexTorusDartBondMate T d).1
  cases hfirst : vertexMask d.1 <;>
    cases hsecond : vertexMask (sixVertexTorusDartBondMate T d).1
  · rfl
  · exact False.elim (by
      have := hreverse hsecond
      simp [hfirst] at this)
  · exact False.elim (by
      have := hforward hfirst
      simp [hsecond] at this)
  · rfl

theorem sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 =
      sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) d.1 d.2 := by
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  have hlocalDisagrees : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hselectedToActive
      (hselected : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true) :
      vertexMask d.1 = true := by
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).2
    exact ⟨d.2, hselected⟩
  have hactiveToSelected (hactive : vertexMask d.1 = true) :
      sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).1 hactive
    exact sixVertexLexDisagreementComponentMask_incident_closure
      T omega eta h d.1 side d.2 hside hlocalDisagrees
  change vertexMask d.1 =
    sixVertexTorusLocalSwitchMask edgeMask d.1 d.2
  cases hvertex : vertexMask d.1 <;>
    cases hedge : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2
  · rfl
  · exact False.elim (by
      have := hselectedToActive hedge
      simp [hvertex] at this)
  · exact False.elim (by
      have := hactiveToSelected hvertex
      simp [hedge] at this)
  · rfl

theorem sixVertexLexDisagreementComponent_fullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    FKColoredFullSwapBondCoherent source
      (sixVertexLexDisagreementComponentVertexMask T
        (source false).arrows (source true).arrows h) := by
  intro d hmask
  apply (fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq source d).2
  by_contra hedge
  have hdisagrees : sixVertexTorusEdgeDisagrees
      (source false).arrows (source true).arrows
      (sixVertexTorusDartEdge T
        (sixVertexTorusDartOfMedialDart d)) := hedge
  have heq := sixVertexLexDisagreementComponentVertexMask_bondMate
    T (source false).arrows (source true).arrows h
    (sixVertexTorusDartOfMedialDart d) hdisagrees
  rw [← sixVertexTorusDartOfMedialDart_bondMate] at heq
  exact hmask heq


end
end StatMech.FrontierD
