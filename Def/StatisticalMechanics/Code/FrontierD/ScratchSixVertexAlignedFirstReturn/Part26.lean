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
import Structure.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part3
open StatMech.FrontierD


namespace ScratchLocalRetieC

noncomputable def canonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn := by
  let hex := exists_canonicalDoubledAlignedOrbitChunkCut
    homega heta hdegree n homegaSector hetaSector hn
  let before := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cut := Classical.choose hex
  let hex := Classical.choose_spec hex
  let after := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cutLeft := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cutRight := Classical.choose hex
  let h := Classical.choose_spec hex
  exact ⟨before, cut, after, cutLeft, cutRight,
    h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end ScratchLocalRetieC
