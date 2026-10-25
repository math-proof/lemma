/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part3


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def triangularTorusSplitEmbedWalk
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusGraph (3 * L)).Walk
      (triangularTorusSplitEmbedVertex L u)
      (triangularTorusSplitEmbedVertex L v) :=
  p.map (triangularTorusSplitEmbedHom L)

end StatMech.FrontierA
