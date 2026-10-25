/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part2


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_outsideConnectorVertexList (dx dy top : ℤ) :
    List (ℤ × ℤ) :=
  [0] ++
    (List.range (top - dy).toNat).map
      (fun k ↦ (1, (k : ℤ))) ++
    (List.range (dx + 2).toNat).map
      (fun k ↦ (1 - (k : ℤ), top - dy)) ++
    (List.range top.toNat).map
      (fun k ↦ (-dx - 1, top - dy - (k : ℤ))) ++
    [(-dx - 1, -dy)]

end StatMech.Onsager
