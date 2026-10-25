/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part2


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def triangularTorusSplitEmbedHom
    (L : Nat) [Fact (2 < L)] :
    kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L) →g
      triangularTorusGraph (3 * L) where
  toFun := triangularTorusSplitEmbedVertex L
  map_rel' := @triangularTorusSplitEmbedVertex_adj L _


end StatMech.FrontierA
