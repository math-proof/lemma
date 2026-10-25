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
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part12
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem alignedRoutingPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) :
    fkLoopPairingCompatible
      (alignedRoutingPairing homega heta hdegree layer v)
      (if layer then eta else omega) v := by
  unfold alignedRoutingPairing
  split
  · rename_i hactive
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    have hdv : d.1.1.1 = v := rfl
    cases layer
    · apply (compatible_iff_fkLoopPairingCompatible omega v _).1
      exact (orientedDartAlignedRetie homega heta hdegree d).compatibleP
    · apply (compatible_iff_fkLoopPairingCompatible eta v _).1
      exact (orientedDartAlignedRetie homega heta hdegree d).compatibleQ
  · cases layer
    · apply (compatible_iff_fkLoopPairingCompatible omega v _).1
      exact localPreferredPairing_compatible _
        (sixVertexLocalIncomingPattern_ice omega homega v)
    · apply (compatible_iff_fkLoopPairingCompatible eta v _).1
      exact localPreferredPairing_compatible _
        (sixVertexLocalIncomingPattern_ice eta heta v)

end ScratchLocalRetieC
