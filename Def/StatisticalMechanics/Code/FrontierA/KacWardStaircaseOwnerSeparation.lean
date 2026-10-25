/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseCorePlacement
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexEdgeSeparation


namespace StatMech.FrontierA

open scoped NNReal Convex

open Set

def kwStairOwner
    {n S : ℕ} [NeZero n] [NeZero S]
    (j : Fin (n * (2 * S))) : Fin n :=
  (finProdFinEquiv.symm j).1

end StatMech.FrontierA
