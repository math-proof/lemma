/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bmm_cluster_omegaClosed (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ∀ u v, u ∈ cluster d ω x → IsOpenEdge d ω u v → v ∈ cluster d ω x := by
  intro u v hu hedge
  rw [mem_cluster] at hu ⊢
  exact hu.trans hedge.connected


theorem bmm_regions_disjoint (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : cluster d ω x ≠ cluster d ω y) :
    Disjoint (cluster d ω x) (cluster d ω y) :=
  bcc_cluster_disjoint_of_ne ω x y hxy


theorem bmm_distinct_neighbours_of_disjoint_regions {a b : Site d} {R S : Set (Site d)}
    (ha : a ∈ R) (hb : b ∈ S) (hdisj : Disjoint R S) : a ≠ b := by
  intro he
  have hmem : a ∈ R ∩ S := ⟨ha, he ▸ hb⟩
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj] at hmem
  exact absurd hmem (Set.notMem_empty _)


end Percolation
end StatMech
