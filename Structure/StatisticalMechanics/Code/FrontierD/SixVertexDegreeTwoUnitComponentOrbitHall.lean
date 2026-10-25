/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexDegreeTwoUnitComponentOrbitPresentation
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Component : Type*) [Fintype Component] (k : Nat) where
  component_card : Fintype.card Component = 2 * k
  sourceEmbedding :
    BooleanLayer Component (k + 1) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  targetEmbedding :
    BooleanLayer Component k ↪
      SixVertexConfigurationPhysicalTarget T middle
  related_iff : forall source target,
    SixVertexDegreeTwoUnitStrandPhysicalRelated
        (sourceEmbedding source) (targetEmbedding target) <->
      booleanMiddleLayerDownRelation source target

end
end StatMech.FrontierD
