module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
public import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part2
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

def FKRectDependsOnOutsideRegion (R : FKRectTorus)
    (S : Set R.Vertex) (B : Set R.Configuration) : Prop :=
  ∀ omega tau : R.Configuration,
    (∀ a : R.EdgeIndex,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)) →
      omega a = tau a) →
    (omega ∈ B ↔ tau ∈ B)


end
end StatMech.FrontierD
