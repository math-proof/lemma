module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
public import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
public import Instance.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part2
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem fkRectInducedGraph_adjMatch (R : FKRectTorus)
    (S : Set R.Vertex) :
    FK.ocd_AdjMatch (fkRectInducedGraph R S) (fkRectTorusGraph R)
      (Subtype.val : FKRectInducedVertex R S → R.Vertex) := by
  intro x y
  rfl


end
end StatMech.FrontierD
