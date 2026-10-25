/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcededgeopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
import Def.StatisticalMechanics.Code.Walls.bc3_regionclosed
open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_region_closed (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (hω : bc3_ClosedUnderOmega ω R) (hG : bc3_ClosedUnderWiring G R) :
    bc3_ClosedUnderRho ω G R := by
  intro x y hxR hxy
  
  obtain ⟨hadj, hval⟩ := hxy
  
  obtain ⟨h0, hcases⟩ := bc3_rho_edge_cases ω G hval
  cases hcases with
  | inl hGmem =>
      
      exact hG hxR hadj hGmem h0
  | inr hωopen =>
      
      exact hω hxR ⟨hadj, hωopen⟩


theorem bc3_omega_open_to_rho {ω : ConfigSpace (Sym2 (Site d))}
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (h : IsOpenEdge d ω x y) (h0 : (0 : Site d) ∉ s(x, y)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
  refine ⟨h.1, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  by_cases hG : s(x, y) ∈ G
  · exact forceOpenFinset_of_mem hG ω
  · rw [forceOpenFinset_of_notMem hG]; exact h.2


theorem bc3_closedUnderWiring_of_rho (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (hϱ : bc3_ClosedUnderRho ω G R) : bc3_ClosedUnderWiring G R := by
  intro x y hxR hadj hGmem h0
  exact hϱ hxR (bkm_dcc_step_open ω G hadj hGmem h0)


theorem bc3_closedUnderOmega_of_rho (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (hϱ : bc3_ClosedUnderRho ω G R) :
    ∀ ⦃x y : Site d⦄, x ∈ R → IsOpenEdge d ω x y → (0 : Site d) ∉ s(x, y) → y ∈ R := by
  intro x y hxR hopen h0
  exact hϱ hxR (bc3_omega_open_to_rho G hopen h0)


theorem bc3_reachable_mem_of_closed (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (hclosed : bc3_ClosedUnderRho ω G R) {x y : Site d} (hxR : x ∈ R)
    (hconn : Connected d (removeSite 0 (forceOpenFinset G ω)) x y) : y ∈ R := by
  
  obtain ⟨w⟩ := hconn
  
  
  induction w with
  | nil => exact hxR
  | cons hstep _ ih =>
      
      
      exact ih (hclosed hxR hstep)


theorem bc3_cluster_subset_of_closed (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (hω : bc3_ClosedUnderOmega ω R) (hG : bc3_ClosedUnderWiring G R)
    {x : Site d} (hxR : x ∈ R) :
    cluster d (removeSite 0 (forceOpenFinset G ω)) x ⊆ R := by
  intro y hy
  exact bc3_reachable_mem_of_closed ω G R (bc3_region_closed ω G R hω hG) hxR hy


theorem bc3_univ_closedUnderRho (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) :
    bc3_ClosedUnderRho ω G (Set.univ : Set (Site d)) :=
  bc3_region_closed ω G Set.univ (fun _ _ _ _ => Set.mem_univ _)
    (fun _ _ _ _ _ _ => Set.mem_univ _)


theorem bc3_cluster_closedUnderRho (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (x : Site d) :
    bc3_ClosedUnderRho ω G (cluster d (removeSite 0 (forceOpenFinset G ω)) x) := by
  intro u v hu hopen
  
  exact hu.trans hopen.connected


theorem bc3_cluster_closedUnderWiring (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (x : Site d) :
    bc3_ClosedUnderWiring G (cluster d (removeSite 0 (forceOpenFinset G ω)) x) :=
  bc3_closedUnderWiring_of_rho ω G _ (bc3_cluster_closedUnderRho ω G x)

end Walls
end StatMech
