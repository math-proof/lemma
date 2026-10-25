/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2


namespace StatMech.FrontierD

noncomputable section

structure FKColoredUnitTransferRoutedKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  targetPairing : Bool -> FKMedialLoopPairing T
  occurrenceCount : Nat
  key : Bool -> Fin occurrenceCount -> T.Vertex × Bool
  key_injective : forall layer, Function.Injective (key layer)
  boundaryIntertwining : FKColoredIndexedOccurrenceBoundaryIntertwining
    source targetPairing occurrenceCount key key_injective
  preservesTotalC :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).PreservesTotalC
  seamDelta_false :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).seamDelta
        false = 1
  seamDelta_true :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).seamDelta
        true = -1


end
end StatMech.FrontierD
