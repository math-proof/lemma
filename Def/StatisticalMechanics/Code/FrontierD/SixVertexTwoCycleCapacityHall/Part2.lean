/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalActualDeficitFineUnionKey
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (source : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexPairFineUnionKey T :=
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  sixVertexPairFineUnionKey (pair.1.1.1, pair.1.2.1)

def sixVertexHorizontalActualSurplusFineUnionKey
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (target : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexPairFineUnionKey T :=
  let pair := sixVertexHorizontalActualSurplusConfigurationPair target
  sixVertexPairFineUnionKey (pair.1.1.1, pair.1.2.1)

def sixVertexHorizontalActualDeficitFineUnionCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) : Nat :=
  Fintype.card {source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualDeficitFineUnionKey source = key}

def sixVertexHorizontalActualSurplusFineUnionCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) : Nat :=
  Fintype.card {target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusFineUnionKey target = key}


def SixVertexHorizontalTwoCycleKeyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade (sourceKeys : Finset (SixVertexPairFineUnionKey T)),
    (∑ key ∈ sourceKeys,
      sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key) <=
    ∑ key ∈ (Finset.univ.filter fun targetKey =>
        exists sourceKey,
          sourceKey ∈ sourceKeys ∧
            SixVertexPairFineUnionKeyTwoCycleRelated sourceKey targetKey),
      sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key


def SixVertexHorizontalTwoCycleKeyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty (FiniteKeyCapacityTransport
    (SixVertexPairFineUnionKey T)
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated)


def SixVertexHorizontalTwoCycleInjectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, exists route : SixVertexPairFineUnionKey T ->
      SixVertexPairFineUnionKey T,
    Function.Injective route /\
      (forall key,
        SixVertexPairFineUnionKeyTwoCycleRelated key (route key)) /\
      forall key,
        sixVertexHorizontalActualDeficitFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade key <=
          sixVertexHorizontalActualSurplusFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade (route key)


end
end StatMech.FrontierD
