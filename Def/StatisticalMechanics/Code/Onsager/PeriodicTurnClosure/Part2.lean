/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_outsideConnector (dx dy top : ℤ) : List (Fin 4) :=
  [0] ++
    List.replicate (top - dy).toNat 1 ++
    List.replicate (dx + 2).toNat 2 ++
    List.replicate top.toNat 3 ++ [0]

end StatMech.Onsager
