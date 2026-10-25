/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitHall
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalProfileDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade
    (A : Finset (SixVertexHorizontalProfileDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card

def SixVertexHorizontalProfileDeficitSupportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade, Exists fun matching :
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight =>
    Function.Injective matching ∧
      forall source, support grade source (matching source)

end
end StatMech.FrontierD
