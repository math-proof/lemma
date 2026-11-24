module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


noncomputable def booleanMatching
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :
    BooleanLayer Component (k + 1) ↪ BooleanLayer Component k :=
  ⟨Classical.choose orbit.exists_booleanMatching,
    (Classical.choose_spec orbit.exists_booleanMatching).1⟩


end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
