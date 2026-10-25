/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalProfileTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ->
        SixVertexHorizontalProfileTokens T grade targetLeft targetRight -> Prop) :
    Prop :=
  forall grade
    (A : Finset
      (SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card


end
end StatMech.FrontierD
