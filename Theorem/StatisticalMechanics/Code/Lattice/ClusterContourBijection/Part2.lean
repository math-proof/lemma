/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.ClusterContourBijection
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_walk_stays_in_K {K : Finset (Site d)} {n : ℕ}
    (hsub : (↑K : Set (Site d)) ⊆ box d n) :
    ∀ {a x : Site d},
      ((hypercubicLattice d).deleteEdges
          ↑(crossEdges (↑K) (bondFinsetTouch d n))).Walk a x →
      a ∈ K → x ∈ K := by
  intro a x w
  induction w with
  | nil => exact fun h => h
  | @cons a b c hab w ih =>
    intro haK
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hadj, hne⟩ := hab
    have hbK : b ∈ K := by
      by_contra hbK
      exact hne (by simpa using ccb_boundary_step_mem_crossEdges hadj haK hbK (hsub haK))
    exact ih hbK


theorem ccb_regionDel_crossEdges_eq {K : Finset (Site d)} {n : ℕ}
    (hconn : IsConnectedCluster K) (hsub : (↑K : Set (Site d)) ⊆ box d n) :
    regionDel d ↑(crossEdges (↑K) (bondFinsetTouch d n)) = (↑K : Set (Site d)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w⟩
    exact ccb_walk_stays_in_K hsub w hconn.1
  · intro x hx
    have hle : latticeOn (↑K : Set (Site d)) ≤
        (hypercubicLattice d).deleteEdges ↑(crossEdges (↑K) (bondFinsetTouch d n)) := by
      intro a b hab
      obtain ⟨hadj, haK, hbK⟩ := hab
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hadj, ?_⟩
      intro hmem
      rw [Finset.mem_coe, crossEdges, Finset.mem_filter, crosses_mk] at hmem
      exact (hmem.2.mp haK) hbK
    exact (hconn.2 x (by simpa using hx)).mono hle


theorem ccb_crossEdges_injOn {n : ℕ} :
    Set.InjOn (fun K : Finset (Site d) => crossEdges (↑K) (bondFinsetTouch d n))
      {K | IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n} := by
  intro K hK K' hK' heq
  simp only [Set.mem_setOf_eq] at hK hK'
  simp only [] at heq
  have e1 := ccb_regionDel_crossEdges_eq hK.1 hK.2
  have e2 := ccb_regionDel_crossEdges_eq hK'.1 hK'.2
  have hreg : regionDel d ↑(crossEdges (↑K) (bondFinsetTouch d n))
       = regionDel d ↑(crossEdges (↑K') (bondFinsetTouch d n)) := by rw [heq]
  rw [e1, e2] at hreg
  exact_mod_cast hreg


end Lattice
end StatMech
