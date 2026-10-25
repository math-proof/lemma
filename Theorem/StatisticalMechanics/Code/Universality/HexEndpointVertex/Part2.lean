/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem hexAWPos_eq_returnPos_mul (c : HexAWCoord) :
    hexAWPos c = (hexAWReturnPos c).value * hexUnit 1 := by
  have h4 : hexUnit 4 = -hexUnit 1 := by
    simpa using hexUnit_add_three 1
  have h0 : hexUnit 0 = -(hexOmega * hexUnit 1) := by
    calc
      hexUnit 0 = hexUnit (0 + 6) := (hexUnit_add_six 0).symm
      _ = hexOmega * hexUnit 4 := by
        simpa using hexUnit_add_two 4
      _ = -(hexOmega * hexUnit 1) := by rw [h4]; ring
  have h2 : hexUnit 2 = -(hexOmega ^ 2 * hexUnit 1) := by
    calc
      hexUnit 2 = hexUnit (2 + 6) := (hexUnit_add_six 2).symm
      _ = hexOmega ^ 2 * hexUnit 4 := by
        simpa using hexUnit_add_four 4
      _ = -(hexOmega ^ 2 * hexUnit 1) := by rw [h4]; ring
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexAWPos, hexAWReturnPos, hexAWBasisI, hexAWBasisJ,
      hexAWAxis, HexReturnCoord.value]
  all_goals
    push_cast
    rw [h4, h0, h2, hexConcrete_omega_cubic]
    ring


end
end StatMech.Universality
