/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (wiredGraph (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n)
      (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
    triHexPlanarFiniteStarVertexComponentLabel n omega u =
      triHexPlanarFiniteStarVertexComponentLabel n omega v := by
  have hreach := triHexPlanarFiniteStar_wired_adj_representative_reachable
    n omega huv
  have hcomponent :
      (triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
          (triHexPlanarFiniteStarRepresentative n omega u) =
        (triHexPlanarFiniteStarWiredSectorGraph n omega).connectedComponentMk
          (triHexPlanarFiniteStarRepresentative n omega v) :=
    SimpleGraph.ConnectedComponent.sound hreach
  rw [wiredGraph_adj] at huv
  rcases huv with hopen | hboundary
  · obtain ⟨z, i, hi, horient⟩ :=
      triHexPlanarFiniteStar_openSub_adj_eq_spoke n omega hopen
    have hnot : triHexPlanarFiniteStarConfigEquiv n omega z ≠
        (false, false, false) := by
      intro hclosed
      rw [hclosed] at hi
      fin_cases i <;> simp [triHexLocalDirection] at hi
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [triHexPlanarFiniteStarVertexComponentLabel, dif_neg hnot]
      exact congrArg Sum.inl hcomponent
    · simp only [triHexPlanarFiniteStarVertexComponentLabel, dif_neg hnot]
      exact congrArg Sum.inl hcomponent
  · rcases u with u | u <;> rcases v with v | v
    · exact hboundary.2.1.elim
    · exact hboundary.2.1.elim
    · exact hboundary.2.2.elim
    · simp only [triHexPlanarFiniteStarVertexComponentLabel]
      exact congrArg Sum.inl hcomponent


end
end StatMech.FK.PeriodicPlanar
