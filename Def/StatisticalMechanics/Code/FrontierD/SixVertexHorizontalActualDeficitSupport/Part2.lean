/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalActualDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade
    (A : Finset (SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card

def SixVertexHorizontalActualDeficitSupportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade, Exists fun matching :
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight =>
    Function.Injective matching ∧
      forall source, support grade source (matching source)

end
end StatMech.FrontierD
