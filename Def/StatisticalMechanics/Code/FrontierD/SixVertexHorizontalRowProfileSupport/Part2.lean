/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalActualDeficitRowProfile
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (source : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowZeroProfile T :=
  sixVertexHorizontalPairRowZeroProfile
    (sixVertexHorizontalActualDeficitPair source)

def sixVertexHorizontalActualSurplusRowProfile
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (target : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowZeroProfile T :=
  sixVertexHorizontalPairRowZeroProfile
    (sixVertexHorizontalActualSurplusPair target)


def sixVertexHorizontalActualRowProfileSupport
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop :=
  fun _ source target =>
    sixVertexHorizontalActualDeficitRowProfile source =
      sixVertexHorizontalActualSurplusRowProfile target


def SixVertexHorizontalRowProfileResidualCapacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (profile : SixVertexHorizontalRowZeroProfile T),
    Fintype.card
        {source : SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualDeficitRowProfile source = profile} <=
      Fintype.card
        {target : SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualSurplusRowProfile target = profile}


end
end StatMech.FrontierD
