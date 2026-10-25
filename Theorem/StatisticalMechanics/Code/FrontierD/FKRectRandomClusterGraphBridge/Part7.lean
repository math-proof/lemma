/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectGraphOpenEdgeCount_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphOpenEdgeCount R (fkRectConfigurationGraphEquiv R omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectGraphOpenEdgeCount fkRectOpenEdgeCount
  symm
  apply Finset.card_bij
      (fun a _ => fkRectEdgeGraphEquiv R a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (fkRectConfigurationGraphEquiv_apply_edge R omega a).trans ha
  · intro a ha b hb hab
    exact (fkRectEdgeGraphEquiv R).injective hab
  · intro e he
    refine ⟨(fkRectEdgeGraphEquiv R).symm e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      simpa [fkRectConfigurationGraphEquiv] using he
    · exact (fkRectEdgeGraphEquiv R).apply_symm_apply e


end
end StatMech.FrontierD
