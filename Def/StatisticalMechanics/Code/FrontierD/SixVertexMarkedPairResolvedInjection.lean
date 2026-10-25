/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection


namespace StatMech.FrontierD

noncomputable section

def sixVertexExplicitResolvedCompatiblePairing
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    SixVertexCompatibleLoopPairing
      (sixVertexArrowPairLayer resolved.1.1.1.1
        resolved.1.1.2.1 layer) :=
  ⟨sixVertexExplicitResolvedPairing resolved.1.2 resolved.2 layer,
    sixVertexExplicitResolvedPairing_compatible
      resolved.1.1.1.2.1 resolved.1.1.2.2.1
      resolved.1.2 resolved.2 layer⟩


def sixVertexExplicitResolvedColoredPair
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    FKColoredLoopPairingPair T := fun layer =>
  (sixVertexExplicitResolvedCompatiblePairing resolved layer).toColored


def sixVertexExplicitResolvedBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    Nat × Nat :=
  (fkColoredLoopPairingPairTotalC
      (sixVertexExplicitResolvedColoredPair resolved),
    fkColoredTrueStrandSlotCount
      (sixVertexExplicitResolvedColoredPair resolved))


def SixVertexExplicitResolvedBigradeFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall k grade,
    Nat.card {source : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k //
      sixVertexExplicitResolvedBigrade source = grade} <=
    Nat.card {target : SixVertexExplicitResolvedMarkedPair
        T targetLeft targetRight k //
      sixVertexExplicitResolvedBigrade target = grade}

end
end StatMech.FrontierD
