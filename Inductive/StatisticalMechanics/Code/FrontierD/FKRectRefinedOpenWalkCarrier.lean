/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedPathReversal
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedRepeatedAppend


namespace StatMech.FrontierD

noncomputable section

inductive FKRectRefinedOpenEdgeBlocks
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    List FKRectIntegralSquareDart -> Prop
  | nil : FKRectRefinedOpenEdgeBlocks R F []
  | consForward (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenEdgeBlocks R F l) :
      FKRectRefinedOpenEdgeBlocks R F
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenEdgeBlocks R F l) :
      FKRectRefinedOpenEdgeBlocks R F
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)


end
end StatMech.FrontierD
