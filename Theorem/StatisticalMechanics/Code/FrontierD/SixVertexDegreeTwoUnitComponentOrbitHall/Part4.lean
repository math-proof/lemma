/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


theorem booleanMatching_related
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1)) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (orbit.sourceEmbedding source)
      (orbit.targetEmbedding (orbit.booleanMatching source)) := by
  apply (orbit.related_iff source (orbit.booleanMatching source)).2
  exact (Classical.choose_spec orbit.exists_booleanMatching).2 source


end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
