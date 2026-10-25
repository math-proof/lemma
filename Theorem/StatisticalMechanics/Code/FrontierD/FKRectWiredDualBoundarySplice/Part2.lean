/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWiredDualAddedEdges_disjoint_openEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    Disjoint (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
      (fkRectWiredDualAddedEdges R omega) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOpen heAdded
  exact (Finset.mem_sdiff.mp heAdded).2 heOpen


theorem fkRectDualConfiguration_forceCutClosed_apply
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) e =
      if e ∈ fkRectDualCutEdges R then true
      else fkRectDualConfigurationEquiv R omega e := by
  rw [fkRectDualConfigurationEquiv_apply,
    fkRectDualConfigurationEquiv_apply]
  by_cases he : e ∈ fkRectDualCutEdges R
  · rw [if_pos he]
    have hcut := (mem_fkRectDualCutEdges_iff R e).1 he
    rw [fkRectForceCutClosed_of_mem R omega _ hcut]
    rfl
  · rw [if_neg he]
    have hcut : fkRectDualEdgeToEdge R e ∉ fkRectTorusCutEdges R := by
      simpa using he
    rw [fkRectForceCutClosed_of_not_mem R omega _ hcut]


theorem fkRectOpenEdges_dual_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdges R
        (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectDualCutEdges R := by
  classical
  ext e
  simp only [fkRectOpenEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  rw [fkRectDualConfiguration_forceCutClosed_apply]
  by_cases he : e ∈ fkRectDualCutEdges R
  · simp [he]
  · simp [he]


theorem fkRectOpenEdges_dual_forceCutClosed_eq_inserted
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdges R
        (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectWiredDualAddedEdges R omega := by
  rw [fkRectOpenEdges_dual_forceCutClosed]
  classical
  ext e
  simp [fkRectWiredDualAddedEdges]


theorem fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) =
      fkRectConfigurationOfEdges R
        (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
          fkRectWiredDualAddedEdges R omega) := by
  rw [← fkRectOpenEdges_dual_forceCutClosed_eq_inserted]
  exact (fkRectConfigurationOfEdges_openEdges R _).symm


end
end StatMech.FrontierD
