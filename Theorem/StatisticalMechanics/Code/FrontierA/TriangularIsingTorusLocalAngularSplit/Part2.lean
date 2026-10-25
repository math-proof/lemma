/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part2


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorusLocalPortOrder_rank
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    kwOrderedPortRank (triangularTorusLocalPortOrder L) p =
      (triangularTorusDirectionRank
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) p))).val := by
  rcases p with ⟨v, i⟩
  unfold kwOrderedPortRank triangularTorusLocalPortOrder
    triangularTorusDirectionRankEquiv
  change (((Fin.castOrderIso
    (triangularTorusOutgoingDart_card L v).symm)
      (triangularTorusDirectionRank
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) ⟨v, i⟩)))).val) = _
  simp


end StatMech.FrontierA
