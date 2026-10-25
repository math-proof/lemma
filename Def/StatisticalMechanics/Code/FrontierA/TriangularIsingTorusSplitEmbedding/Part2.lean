/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def triangularTorusSplitEmbedVertex
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    ZMod (3 * L) × ZMod (3 * L) :=
  let a := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p)
  ((3 * p.1.1.val + (triangularTorusSplitOffset a).1 : Nat),
    (3 * p.1.2.val + (triangularTorusSplitOffset a).2 : Nat))

end StatMech.FrontierA
