/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc7nocrossing
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc8_clusters_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Connected d (removeSite 0 ω) x y) :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact h (hwx.trans hwy.symm)


theorem bc8_connected_of_not_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y)) :
    Connected d (removeSite 0 ω) x y := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨w, hwx, hwy⟩ := h
  rw [mem_cluster] at hwx hwy
  exact hwx.trans hwy.symm


theorem bc8_cut_disjoint_iff_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) ↔
      ¬ Connected d (removeSite 0 ω) x y :=
  ⟨fun hdisj hconn => (Set.disjoint_left.mp hdisj
      (self_mem_cluster _ x) (mem_cluster.mpr hconn.symm)),
   bc8_clusters_disjoint⟩


theorem bc8_cut_ne_iff_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      ¬ Connected d (removeSite 0 ω) x y := by
  constructor
  · intro hne hconn
    exact hne (cluster_eq_of_connected hconn)
  · intro hdis heq
    
    have hy : y ∈ cluster d (removeSite 0 ω) x := by
      rw [heq]; exact self_mem_cluster _ y
    exact hdis (mem_cluster.mp hy)


theorem bc8_cut_ne_iff_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) :=
  bc8_cut_ne_iff_disconnected.trans bc8_cut_disjoint_iff_disconnected.symm


theorem bc8_disjoint_of_cut_ne {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) :=
  bc8_cut_ne_iff_disjoint.mp hne


theorem bc8_cut_no_crossing {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  bc7_cut_no_crossing hne


theorem bc8_cut_no_crossing_of_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Connected d (removeSite 0 ω) x y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  bc8_cut_no_crossing (bc8_cut_ne_iff_disconnected.mpr h)


end Walls
end StatMech
