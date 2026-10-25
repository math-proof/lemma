/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.jwd_contoureulerone
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc4_cycleGraph_nullity_one (n : ℕ) : nullity (cycleGraph (n + 3)) = 1 := by
  unfold nullity
  have hc : Nat.card (cycleGraph (n + 3)).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected cycleGraph_connected
  have he : (cycleGraph (n + 3)).edgeSet.ncard = n + 3 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, cycleGraph_card_edges]
  rw [hc, he]
  simp [Nat.card_eq_fintype_card]


theorem kc4_cycleGraph_cyclomaticNumber_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  unfold cyclomaticNumber
  rw [cycleGraph_card_edges n]
  simp


theorem kc4_cycleGraph_boundedFaceCount_two (n : ℕ) :
    faceCount (cycleGraph (n + 3)) = 2 := by
  rw [faceCount, kc4_cycleGraph_nullity_one]


end Walls
end StatMech
