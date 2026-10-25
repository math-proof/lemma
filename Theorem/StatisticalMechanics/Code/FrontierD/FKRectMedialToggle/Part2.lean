/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeInsertion
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle.Part2
open Finset


namespace StatMech.FrontierD

@[simp] theorem fkRectTorusMedialEdgeEquiv_vertexOfEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusMedialEdgeEquiv R (fkRectMedialVertexOfEdge R e) = e := by
  simp [fkRectMedialVertexOfEdge]


theorem fkRectConfigurationToMedialPairing_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (he : e ∉ F) :
    fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R (insert e F)) =
      fkMedialTogglePairingAt
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkRectMedialVertexOfEdge R e) := by
  funext w
  by_cases hw : w = fkRectMedialVertexOfEdge R e
  · subst w
    rw [fkMedialTogglePairingAt_self]
    simp only [fkRectConfigurationToMedialPairing_apply,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    have hnew : fkRectConfigurationOfEdges R (insert e F) e = true := by
      simp [fkRectConfigurationOfEdges]
    have hold : fkRectConfigurationOfEdges R F e = false := by
      simp [fkRectConfigurationOfEdges, he]
    rw [hnew, hold]
    cases fkRectClosedPairingAtEdge e <;> rfl
  · have hindex : fkRectTorusMedialEdgeEquiv R w ≠ e := by
      intro h
      apply hw
      exact (fkRectTorusMedialEdgeEquiv R).injective <| by
        rw [h, fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    rw [fkMedialTogglePairingAt_of_ne _ hw]
    simp only [fkRectConfigurationToMedialPairing_apply]
    have hmem :
        (fkRectTorusMedialEdgeEquiv R w ∈ insert e F) ↔
          fkRectTorusMedialEdgeEquiv R w ∈ F := by
      simp [hindex]
    have hconfig :
        fkRectConfigurationOfEdges R (insert e F)
            (fkRectTorusMedialEdgeEquiv R w) =
          fkRectConfigurationOfEdges R F
            (fkRectTorusMedialEdgeEquiv R w) := by
      simp only [fkRectConfigurationOfEdges]
      rw [decide_eq_decide]
      exact hmem
    rw [hconfig]

end StatMech.FrontierD
