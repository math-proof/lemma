/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcr_regionComponents_finite (P : PlanarZ2Subgraph) :
    Finite (regionGraph (imageGraph P)).ConnectedComponent := by
  classical
  set R := outerBoxRadius P with hR
  set RG := regionGraph (imageGraph P) with hRG
  set S : Set (Site 2) := box 2 R ∪ {beacon 2 R} with hS
  have hSfin : S.Finite := (box_finite 2 R).union (Set.finite_singleton _)
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 R
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hxbox
    have hmk : RG.connectedComponentMk x = outerRegion P := exterior_in_outerRegion P hxext
    refine ⟨beacon 2 R, Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 R) = c
    have hbeac : RG.connectedComponentMk (beacon 2 R) = outerRegion P := rfl
    rw [hbeac, ← hmk]
    exact hx

end Lattice
end StatMech
