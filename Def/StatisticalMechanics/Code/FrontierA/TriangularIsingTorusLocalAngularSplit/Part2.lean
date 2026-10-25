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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit


namespace StatMech.FrontierA

open SimpleGraph


noncomputable def triangularTorusLocalPortOrder
    (L : Nat) [Fact (2 < L)] : KWPortOrder (triangularTorusGraph L) :=
  fun v =>
    (Fintype.equivFin
      (KWOutgoingDart (G := triangularTorusGraph L) v)).symm |>.trans
      ((triangularTorusOutgoingDirectionEquiv L v).trans
        triangularTorusDirectionRankEquiv) |>.trans
      (Fin.castOrderIso (triangularTorusOutgoingDart_card L v).symm).toEquiv

end StatMech.FrontierA
