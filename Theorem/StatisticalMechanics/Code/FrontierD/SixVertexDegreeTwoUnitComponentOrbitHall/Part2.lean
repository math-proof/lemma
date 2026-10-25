/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


@[simp] theorem sourceEquiv_val
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (source : BooleanLayer Component (k + 1)) :
    (orbit.sourceEquiv source).1 = orbit.sourceEmbedding source := by
  rfl

@[simp] theorem targetEquiv_val
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k)
    (target : BooleanLayer Component k) :
    (orbit.targetEquiv target).1 = orbit.targetEmbedding target := by
  rfl


end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
