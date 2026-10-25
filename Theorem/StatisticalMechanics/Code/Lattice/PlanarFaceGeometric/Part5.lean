/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
open SimpleGraph Set


namespace StatMech.Lattice

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


theorem geometricRegionCount_eq_nullity (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    geometricRegionCount P = nullity P.G := by
  obtain ⟨e⟩ := hJ
  unfold geometricRegionCount
  rw [Nat.card_eq_of_equiv_fin e]


theorem faceCount_eq_geometric_regions (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    faceCount P.G = geometricRegionCount P + 1 := by
  rw [geometricRegionCount_eq_nullity P hJ, faceCount]


theorem euler_geometric_regions (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1)
      = 1 + Nat.card P.G.ConnectedComponent := by
  have h := euler_general P.G
  have hfc : (faceCount P.G : ℤ) = (geometricRegionCount P : ℤ) + 1 := by
    rw [faceCount_eq_geometric_regions P hJ]; push_cast; ring
  rw [hfc] at h
  linarith


theorem euler_geometric_regions_connected (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) (hC : P.G.Connected) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 2 := by
  have h := euler_geometric_regions P hJ
  rw [card_components_eq_one_of_connected hC] at h
  push_cast at h ⊢; linarith

end StatMech.Lattice
