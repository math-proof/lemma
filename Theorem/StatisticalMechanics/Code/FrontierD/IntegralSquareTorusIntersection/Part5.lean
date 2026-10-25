/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part5
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem intersection_eq_zero_of_locallyDisjoint
    {C D : IntegralSquareTorusCycle L} (h : C.LocallyDisjoint D) :
    C.intersection D = 0 := by
  unfold intersection
  apply Finset.sum_eq_zero
  intro p _
  rcases h p with hC | hD
  · rw [hC.1, hC.2]
    ring
  · rw [hD.1, hD.2]
    ring


theorem flux_det_eq_zero_of_locallyDisjoint
    {C D : IntegralSquareTorusCycle L} (h : C.LocallyDisjoint D) :
    C.xFlux (-1) * D.yFlux (-1) -
      C.yFlux (-1) * D.xFlux (-1) = 0 := by
  rw [← C.intersection_eq_flux_det D,
    C.intersection_eq_zero_of_locallyDisjoint h]


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
