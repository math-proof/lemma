/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualEdgeCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedPathReversal
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier


namespace StatMech.FrontierD

noncomputable section

inductive FKRectRefinedDualOpenEdgeBlocks
    (R : FKRectTorus) (omega : R.Configuration) :
    List FKRectIntegralSquareDart -> Prop
  | nil : FKRectRefinedDualOpenEdgeBlocks R omega []
  | consForward (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenEdgeBlocks R omega l) :
      FKRectRefinedDualOpenEdgeBlocks R omega
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenEdgeBlocks R omega l) :
      FKRectRefinedDualOpenEdgeBlocks R omega
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedDualEdgeDarts R d)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)


inductive FKRectRefinedDualOpenWalkBlocksAlong
    (R : FKRectTorus) (omega : R.Configuration) :
    {x y : R.Vertex} ->
      (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk x y ->
      (Int × Int) -> (Int × Int) ->
      List FKRectIntegralSquareDart -> Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega
        ((.nil : (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R omega)).Walk x x)) p p []
  | consForward {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk y z}
      (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).1.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).2.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenWalkBlocksAlong R omega w q r l) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega (.cons hxy w) p r
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk y z}
      (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).2.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).1.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenWalkBlocksAlong R omega w q r l) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega (.cons hxy w) p r
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedDualEdgeDarts R d)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)

end
end StatMech.FrontierD
