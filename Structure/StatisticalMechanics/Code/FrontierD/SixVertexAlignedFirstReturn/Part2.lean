/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part24
open StatMech.FrontierD


namespace StatMech.FrontierD

structure DoubledAlignedUnitOrbitSplit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) where
  first : List (DoubledAlignedState omega eta)
  second : List (DoubledAlignedState omega eta)
  split : alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree) = first ++ second
  first_charge : (first.map (doubledAlignedCharge hdegree)).sum = 1
  second_charge : (second.map (doubledAlignedCharge hdegree)).sum = 1

end StatMech.FrontierD
