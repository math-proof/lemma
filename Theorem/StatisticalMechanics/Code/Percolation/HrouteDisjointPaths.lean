/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem isOpenEdge_removeSite_forceOpen_step (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (hmem : s(x, y) ∈ G)
    (h0 : (0 : Site d) ∉ s(x, y)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  exact forceOpenFinset_of_mem hmem ω


theorem connected_removeSite_forceOpen_of_corridor (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {p q : Site d}
    (h : Relation.ReflTransGen
      (fun u v => (hypercubicLattice d).Adj u v ∧ s(u, v) ∈ G ∧ (0 : Site d) ∉ s(u, v)) p q) :
    Connected d (removeSite 0 (forceOpenFinset G ω)) p q := by
  induction h with
  | refl => exact connected_rfl
  | tail _ hstep ih =>
    obtain ⟨hadj, hmem, h0⟩ := hstep
    exact ih.trans (IsOpenEdge.connected (isOpenEdge_removeSite_forceOpen_step ω G hadj hmem h0))


end DisjointPaths
end Percolation
end StatMech
