/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexExplicitResolvedUnitTransferRoutedKey
    {T : EvenTorus} {lower upper : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T lower upper k) :=
  FKColoredUnitTransferRoutedKey
    (sixVertexExplicitResolvedColoredPair resolved)

end
end StatMech.FrontierD
