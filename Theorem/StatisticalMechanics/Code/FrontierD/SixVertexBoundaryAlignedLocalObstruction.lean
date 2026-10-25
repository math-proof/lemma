/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBoundaryAlignedLocalObstruction


namespace StatMech.FrontierD

theorem boundaryAlignedObstructionP_ice :
    boundaryAlignedObstructionP.Ice := by decide

theorem boundaryAlignedObstructionQ_ice :
    boundaryAlignedObstructionQ.Ice := by decide

theorem boundaryAlignedObstruction_degree_two :
    (sixVertexLocalDisagreementSides
      boundaryAlignedObstructionP boundaryAlignedObstructionQ).card = 2 := by
  decide

theorem boundaryAlignedObstruction_compatible :
    compatible false boundaryAlignedObstructionP /\
      compatible true boundaryAlignedObstructionQ := by
  unfold compatible boundaryAlignedObstructionP
    boundaryAlignedObstructionQ
  decide


theorem boundaryAlignedObstruction_target_patterns
    (targetPairingP targetPairingQ : Bool) :
    boundaryAlignedTransportedLocalPattern
        boundaryAlignedObstructionP boundaryAlignedObstructionQ
        false true false 2 false true
        targetPairingP targetPairingQ false = ![true, true, false, false] /\
      boundaryAlignedTransportedLocalPattern
        boundaryAlignedObstructionP boundaryAlignedObstructionQ
        false true false 2 false true
        targetPairingP targetPairingQ true = ![false, false, true, true] := by
  cases targetPairingP <;> cases targetPairingQ <;>
    decide

theorem boundaryAlignedObstruction_target_ice
    (targetPairingP targetPairingQ layer : Bool) :
    (boundaryAlignedTransportedLocalPattern
      boundaryAlignedObstructionP boundaryAlignedObstructionQ
      false true false 2 false true
      targetPairingP targetPairingQ layer).Ice := by
  cases targetPairingP <;> cases targetPairingQ <;> cases layer <;>
    decide


theorem boundaryAlignedTransport_no_exact_localC
    (targetPairingP targetPairingQ : Bool) :
    localCIndicator
          (boundaryAlignedTransportedLocalPattern
            boundaryAlignedObstructionP boundaryAlignedObstructionQ
            false true false 2 false true
            targetPairingP targetPairingQ false) +
        localCIndicator
          (boundaryAlignedTransportedLocalPattern
            boundaryAlignedObstructionP boundaryAlignedObstructionQ
            false true false 2 false true
            targetPairingP targetPairingQ true) ≠
      localCIndicator boundaryAlignedObstructionP +
        localCIndicator boundaryAlignedObstructionQ := by
  cases targetPairingP <;> cases targetPairingQ <;>
    decide

end StatMech.FrontierD
