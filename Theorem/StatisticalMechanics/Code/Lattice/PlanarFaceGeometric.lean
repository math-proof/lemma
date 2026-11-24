module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Def.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Lattice

@[simp] theorem regionGraph_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (regionGraph G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet := Iff.rfl


theorem regionGraph_le_dual (G : SimpleGraph (Site 2)) :
    regionGraph G ≤ hypercubicLattice 2 := fun _ _ h => h.1


end StatMech.Lattice
