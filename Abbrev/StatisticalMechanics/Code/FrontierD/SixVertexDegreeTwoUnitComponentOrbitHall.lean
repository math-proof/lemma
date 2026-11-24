module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall
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


abbrev SourceOrbit
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :=
  Set.range orbit.sourceEmbedding


abbrev TargetOrbit
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) :=
  Set.range orbit.targetEmbedding


end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
