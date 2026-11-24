module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
public import Mathlib.Data.Finset.SymmDiff
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand
open Finset SimpleGraph
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev sixVertexDegreeTwoOrientedComponentEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexTorusEdge T :=
  sixVertexTorusDartEdge T
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1


end
end StatMech.FrontierD
