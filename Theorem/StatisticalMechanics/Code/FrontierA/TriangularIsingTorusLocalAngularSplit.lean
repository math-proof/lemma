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
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorusOutgoingDart_card
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    Fintype.card (KWOutgoingDart (G := triangularTorusGraph L) v) = 6 := by
  simpa using Fintype.card_congr (triangularTorusOutgoingDirectionEquiv L v)


end StatMech.FrontierA
