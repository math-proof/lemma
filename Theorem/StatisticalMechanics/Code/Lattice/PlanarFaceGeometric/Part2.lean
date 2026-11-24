module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Def.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part2
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

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


@[simp] theorem imageGraph_adj (P : PlanarZ2Subgraph) (a b : Site 2) :
    (imageGraph P).Adj a b ↔ ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b :=
  Iff.rfl


theorem imageGraph_le_lattice (P : PlanarZ2Subgraph) :
    imageGraph P ≤ hypercubicLattice 2 := by
  rintro a b ⟨x, y, hadj, rfl, rfl⟩
  exact P.isSub hadj


end StatMech.Lattice
