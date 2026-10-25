/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


theorem related_equiv
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1))
    (target : BooleanLayer Component k) :
    orbit.Related (orbit.sourceEquiv source) (orbit.targetEquiv target) <->
      booleanMiddleLayerDownRelation source target := by
  exact orbit.related_iff source target


theorem exists_booleanMatching
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    ∃ matching : BooleanLayer Component (k + 1) →
        BooleanLayer Component k,
      Function.Injective matching ∧
        ∀ source, booleanMiddleLayerDownRelation source (matching source) := by
  have hBoolean := booleanMiddleLayerDownRelation_hall k orbit.component_card
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective
    (booleanMiddleLayerDownRelation
      (Component := Component) (k := k))).mp hBoolean


end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
