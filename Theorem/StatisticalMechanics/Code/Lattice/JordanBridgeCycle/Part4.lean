/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jbc_bridgeCycleDual_of_reduced (P : PlanarZ2Subgraph) (h : jbc_ReducedBridgeCycle P) :
    jei_BridgeCycleDual P := by
  intro K hKle x y hadjG hnotK
  rw [jbc_dualSide_iff_primalAvoid P K hadjG.ne]
  exact h K hKle hadjG hnotK


theorem jbc_discreteJordan_of_reduced (P : PlanarZ2Subgraph) (h : jbc_ReducedBridgeCycle P) :
    DiscreteJordanSeparation P :=
  jei_discreteJordan_of_sync P (jbc_bridgeCycleDual_of_reduced P h)


theorem jbc_reducedBridgeCycle_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jbc_ReducedBridgeCycle P := by
  intro K _ x y hadjG _
  rw [hG] at hadjG
  exact absurd hadjG (by simp)


theorem jbc_discreteJordan_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    DiscreteJordanSeparation P :=
  jbc_discreteJordan_of_reduced P (jbc_reducedBridgeCycle_of_bot hG)


end Lattice
end StatMech
