/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFiniteDualComparison
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
import Def.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part2
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

@[simp] theorem triHexPlanarFiniteStarExtendEdge_edgeIncl
    (m : Nat)
    (omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V))
    (e : Sym2 (triHexPlanarFiniteStarPlanar m).V) :
    triHexPlanarFiniteStarExtendEdge m omega
      (triHexPlanarFiniteStarEdgeIncl m e) = omega e := by
  unfold triHexPlanarFiniteStarExtendEdge
  rw [dif_pos ⟨e, rfl⟩]
  congr 1
  exact triHexPlanarFiniteStarEdgeIncl_injective m
    (Set.mem_range.mp
      (show triHexPlanarFiniteStarEdgeIncl m e ∈
        Set.range (triHexPlanarFiniteStarEdgeIncl m) from ⟨e, rfl⟩)).choose_spec

theorem monotone_triHexPlanarFiniteStarExtendEdge (m : Nat) :
    Monotone (triHexPlanarFiniteStarExtendEdge m) := by
  intro omega eta home e
  unfold triHexPlanarFiniteStarExtendEdge
  by_cases he : e ∈ Set.range (triHexPlanarFiniteStarEdgeIncl m)
  · rw [dif_pos he, dif_pos he]
    exact home _
  · rw [dif_neg he, dif_neg he]


end
end StatMech.FK.PeriodicPlanar
