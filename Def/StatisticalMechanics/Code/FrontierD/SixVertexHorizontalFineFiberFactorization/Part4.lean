/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalFineRowProfileSignedSum
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) : Int :=
  (sixVertexHorizontalFineRowProfileSectorPairSum
      T targetLeft targetRight profile : Int) -
    sixVertexHorizontalFineRowProfileSectorPairSum
      T sourceLeft sourceRight profile


end
end StatMech.FrontierD
