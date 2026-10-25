/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part24
open StatMech.FrontierD


namespace ScratchLocalRetieC

structure CanonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) where
  before : List (List (DoubledAlignedState omega eta))
  cut : List (DoubledAlignedState omega eta)
  after : List (List (DoubledAlignedState omega eta))
  cutLeft : List (DoubledAlignedState omega eta)
  cutRight : List (DoubledAlignedState omega eta)
  orbitLists : alignedPermOrderedAllOrbitLists
      (doubledAlignedFirstReturnPerm homega heta hdegree) =
    before ++ cut :: after
  cut_eq : cut = cutLeft ++ cutRight
  selected_eq : canonicalDoubledAlignedSelectedStates
      homega heta hdegree n homegaSector hetaSector hn =
    before.flatten ++ cutLeft
  complement_eq :
    (canonicalDoubledAlignedUnitOrbitSplit homega heta hdegree n
      homegaSector hetaSector hn).second =
      cutRight ++ after.flatten

end ScratchLocalRetieC
