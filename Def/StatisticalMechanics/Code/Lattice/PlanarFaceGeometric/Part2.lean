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
import Structure.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric
open SimpleGraph Set


namespace StatMech.Lattice

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


noncomputable def imageGraph (P : PlanarZ2Subgraph) : SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := by
    constructor
    rintro a b ⟨x, y, hadj, rfl, rfl⟩
    exact ⟨y, x, hadj.symm, rfl, rfl⟩
  loopless := ⟨by
    rintro a ⟨x, y, hadj, hx, hy⟩
    have : x = y := P.emb.injective (hx.trans hy.symm)
    exact P.G.irrefl (this ▸ hadj)⟩

end StatMech.Lattice
