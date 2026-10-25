/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def squareTorusPositiveEdgeMap (L : Nat) [Fact (2 < L)] :
    ((ZMod L × ZMod L) × Fin 2) →
      {edge // edge ∈ (onsTorusGraph L).edgeFinset} :=
  fun p ↦ ⟨ons_portEdge L (p.1, squareTorusPositiveDirection p.2),
    ons_portEdge_mem_edgeFinset L _⟩

end StatMech.FrontierA
