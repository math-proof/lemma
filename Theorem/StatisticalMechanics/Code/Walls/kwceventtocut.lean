/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising


theorem kwc_crossEdge_symm_eq_map (e : Sym2 (Site 2)) :
    crossEdge.symm e = Sym2.map rot90Inv e := by
  rfl


theorem kwc_rot90Iso_symm_apply (x : Site 2) : rot90Iso.symm x = rot90Inv x := by
  rfl


theorem kwc_mapped_walk_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
    (W.map rot90Iso.symm.toHom).edges
      = W.edges.map crossEdge.symm := by
  rw [SimpleGraph.Walk.edges_map]
  apply List.map_congr_left
  intro e _
  rw [kwc_crossEdge_symm_eq_map]
  rfl


theorem kwc_pullback_eq_mapped_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
    (W.edges.toFinset).image crossEdge.symm
      = (W.map rot90Iso.symm.toHom).edges.toFinset := by
  rw [kwc_mapped_walk_edges W]
  ext e
  rw [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, List.mem_toFinset.mp hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, List.mem_toFinset.mpr hg, rfl⟩


end Walls
end StatMech
