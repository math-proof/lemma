/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3


namespace StatMech.FrontierD

noncomputable section

theorem FKRectDependsOnOutsideRegion.inter
    (R : FKRectTorus) (S : Set R.Vertex)
    {A B : Set R.Configuration}
    (hA : FKRectDependsOnOutsideRegion R S A)
    (hB : FKRectDependsOnOutsideRegion R S B) :
    FKRectDependsOnOutsideRegion R S (A ∩ B) := by
  intro omega tau hot
  exact and_congr (hA omega tau hot) (hB omega tau hot)

theorem FKRectDependsOnOutsideRegion.compl
    (R : FKRectTorus) (S : Set R.Vertex)
    {A : Set R.Configuration}
    (hA : FKRectDependsOnOutsideRegion R S A) :
    FKRectDependsOnOutsideRegion R S Aᶜ := by
  intro omega tau hot
  exact not_congr (hA omega tau hot)


end
end StatMech.FrontierD
