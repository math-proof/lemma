/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part10
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_imageHom (P : PlanarZ2Subgraph) : P.G →g imageGraph P where
  toFun := P.emb
  map_rel' := by
    intro x y hxy
    exact ⟨x, y, hxy, rfl, rfl⟩


noncomputable def kwg_latticeWalk (P : PlanarZ2Subgraph) {x y : P.V}
    (p : P.G.Walk x y) :
    (hypercubicLattice 2).Walk (P.emb x) (P.emb y) :=
  (p.map (kwg_imageHom P)).mapLe (imageGraph_le_lattice P)


end Ising
end StatMech
