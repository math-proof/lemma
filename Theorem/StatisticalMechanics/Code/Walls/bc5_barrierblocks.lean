/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.bc5_barrierblocks
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc5_cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (a : Site d) (ha : a ∈ R) (hcl : bc5_AdjClosed ϱ R) :
    cluster d ϱ a ⊆ R :=
  cluster_subset_of_adjClosed ϱ R a ha hcl


theorem bc5_mem_of_connected (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hconn : Connected d ϱ p q) :
    q ∈ R :=
  bc5_cluster_subset_of_adjClosed ϱ R p hp hcl (by rwa [mem_cluster])


theorem bc5_barrier_blocks (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q :=
  fun hconn => hq (bc5_mem_of_connected ϱ R p q hcl hp hconn)


theorem bc5_barrier_blocks_symm (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ q p :=
  fun h => bc5_barrier_blocks ϱ R p q hcl hp hq h.symm


theorem bc5_disconnected_of_barrier_split (ϱ : ConfigSpace (Sym2 (Site d)))
    (R : Set (Site d)) (p q : Site d)
    (hcl : bc5_AdjClosed ϱ R) (hp : p ∈ R) (hq : q ∉ R) :
    ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p :=
  ⟨bc5_barrier_blocks ϱ R p q hcl hp hq, bc5_barrier_blocks_symm ϱ R p q hcl hp hq⟩


theorem bc5_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc5_AdjClosed ϱ (cluster d ϱ w) :=
  fun _ _ hu hadj => mng_cluster_adjClosed ϱ w hu hadj


theorem bc5_compl_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d) :
    bc5_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
  intro u v hu hadj hv
  exact hu (mng_cluster_adjClosed ϱ w hv hadj.symm)


theorem bc5_barrier_blocks_iff_cluster (ϱ : ConfigSpace (Sym2 (Site d))) (p q : Site d) :
    (¬ Connected d ϱ p q) ↔
      ∃ R : Set (Site d), bc5_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
  constructor
  · intro hncon
    refine ⟨cluster d ϱ p, bc5_cluster_adjClosed ϱ p, self_mem_cluster ϱ p, ?_⟩
    rw [mem_cluster]; exact hncon
  · rintro ⟨R, hcl, hp, hq⟩
    exact bc5_barrier_blocks ϱ R p q hcl hp hq


end Walls
end StatMech
