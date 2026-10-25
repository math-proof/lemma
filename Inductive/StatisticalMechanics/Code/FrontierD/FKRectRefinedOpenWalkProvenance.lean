/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenWalkCarrier


namespace StatMech.FrontierD

noncomputable section

inductive FKRectRefinedOpenWalkBlocksAlong
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    {x y : R.Vertex} ->
      (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y ->
      (Int × Int) -> (Int × Int) ->
      List FKRectIntegralSquareDart -> Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectRefinedOpenWalkBlocksAlong R F
        ((.nil : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk x x)) p p []
  | consForward {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk y z}
      (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).1.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).2.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenWalkBlocksAlong R F w q r l) :
      FKRectRefinedOpenWalkBlocksAlong R F (.cons hxy w) p r
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk y z}
      (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).2.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).1.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenWalkBlocksAlong R F w q r l) :
      FKRectRefinedOpenWalkBlocksAlong R F (.cons hxy w) p r
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)


end
end StatMech.FrontierD
