/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.cycboundary.Part4
import Def.StatisticalMechanics.Code.Walls.arccontiguity
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


section BoundaryArc

variable {K : Finset (Site 2)} {c a₀ : Site 2}


theorem arc_endpoints_reachable_offPatch
    (hcyc : cyc_BoundaryCycle (↑K : Set (Site 2)))
    {x y : Site 2} (hxy : x ≠ y)
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk x y) (hp : p.IsPath)
    (hint : ∀ w ∈ p.support, w ≠ x → w ≠ y → ats_faceHasCorner c w)
    (hpatch : ∀ w : Site 2, ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support → w ∈ p.support)
    (hx : x ∈ arr_offPatchSet c) (hy : y ∈ arr_offPatchSet c) :
    ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  
  let G : SimpleGraph (Site 2) := faceBoundaryGraph (↑K : Set (Site 2))
  have hGe : G = faceBoundaryGraph (↑K : Set (Site 2)) := rfl
  have hGcyc : G.IsCycles := cyc_isCycles_of_boundaryCycle hcyc
  
  have hpn : ¬ p.Nil := Walk.not_nil_of_ne hxy
  have hxsupp : x ∈ G.support := ⟨p.snd, p.adj_snd hpn⟩
  have hysupp : y ∈ G.support := by
    have := p.reverse.adj_snd (by simpa using hpn)
    exact ⟨p.reverse.snd, this⟩
  
  obtain ⟨T, hsuppT⟩ :=
    exists_finset_support_faceBoundaryGraph (↑K : Set (Site 2)) (K : Set (Site 2)).toFinite
  haveI : Fintype (T : Set (Site 2)) := FinsetCoe.fintype T
  let H : SimpleGraph (T : Set (Site 2)) := G.induce (T : Set (Site 2))
  have hHe : H = G.induce (T : Set (Site 2)) := rfl
  
  have hpsuppT : ∀ w ∈ p.support, w ∈ (T : Set (Site 2)) := by
    intro w hw
    
    rcases eq_or_ne w x with rfl | hwx
    · exact hsuppT hxsupp
    rcases eq_or_ne w y with rfl | hwy
    · exact hsuppT hysupp
    · 
      obtain ⟨n, hgv, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hw
      have hn0 : n ≠ 0 := fun h => hwx (by rw [h, Walk.getVert_zero] at hgv; exact hgv.symm)
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hlt : n - 1 < p.length := by
        have hnlen : n ≠ p.length := fun h => hwy (by rw [h, Walk.getVert_length] at hgv; exact hgv.symm)
        lia
      have hadj := p.adj_getVert_succ hlt
      rw [Nat.sub_add_cancel hnpos, hgv] at hadj
      exact hsuppT ⟨_, hadj.symm⟩
  
  have hHcyc : H.IsCycles := by
    intro v hv
    
    obtain ⟨w, hw⟩ := hv
    have hvG : G.Adj (v : Site 2) (w : Site 2) := hw
    have hvsupp : (v : Site 2) ∈ G.support := ⟨_, hvG⟩
    
    have hGnc : (G.neighborSet (v : Site 2)).ncard = 2 :=
      cyc_neighborSet_ncard_of_degree_two (cyc_degreeTwo hcyc hvsupp)
    
    
    have himg : G.neighborSet (v : Site 2) = Subtype.val '' (H.neighborSet v) := by
      ext z
      simp only [Set.mem_image, SimpleGraph.mem_neighborSet]
      constructor
      · intro hz
        
        have hzsupp : z ∈ G.support := ⟨_, hz.symm⟩
        have hzT : z ∈ (T : Set (Site 2)) := hsuppT hzsupp
        exact ⟨⟨z, hzT⟩, hz, rfl⟩
      · rintro ⟨⟨u, huT⟩, hadj, rfl⟩
        exact hadj
    have hbij : (H.neighborSet v).ncard = (G.neighborSet (v : Site 2)).ncard := by
      rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [hbij, hGnc]
  
  set xH : (T : Set (Site 2)) := ⟨x, hpsuppT x p.start_mem_support⟩ with hxH
  set yH : (T : Set (Site 2)) := ⟨y, hpsuppT y p.end_mem_support⟩ with hyH
  set pH : H.Walk xH yH := p.induce (T : Set (Site 2)) hpsuppT with hpH
  
  have hpHsupp_eq : pH.support = p.support.attachWith _ hpsuppT := by
    rw [hpH]; exact p.support_induce hpsuppT
  
  have hpnodup : p.support.Nodup := hp.support_nodup
  
  have hpHpath : pH.IsPath := by
    rw [Walk.isPath_def, hpHsupp_eq]
    
    apply List.Nodup.of_map (Subtype.val)
    have hmapval : (p.support.attachWith _ hpsuppT).map Subtype.val = p.support := by
      simp [List.attachWith, List.map_pmap]
    rw [hmapval]; exact hpnodup
  have hxyH : xH ≠ yH := fun h => hxy (Subtype.ext_iff.mp h)
  
  set DH : Set (T : Set (Site 2)) := {w | w ∈ pH.support ∧ w ≠ xH ∧ w ≠ yH} with hDH
  have hxDH : xH ∈ (DHᶜ : Set (T : Set (Site 2))) := by
    simp only [Set.mem_compl_iff, hDH, Set.mem_setOf_eq, not_and]; tauto
  have hyDH : yH ∈ (DHᶜ : Set (T : Set (Site 2))) := by
    simp only [Set.mem_compl_iff, hDH, Set.mem_setOf_eq, not_and]; tauto
  
  have hEng := arc_reachable_induce_compl_pathInterior hHcyc hxyH pH hpHpath hxDH hyDH
  
  obtain ⟨qH⟩ := hEng
  
  
  set embD := SimpleGraph.Embedding.induce (G := H) (DHᶜ : Set (T : Set (Site 2))) with hembD
  set qH' : H.Walk xH yH := qH.map embD.toHom with hqH'
  have hqH'supp : qH'.support = qH.support.map embD.toHom := by
    rw [hqH']; exact SimpleGraph.Walk.support_map (p := qH) (f := embD.toHom)
  have hqH'avoid : ∀ z ∈ qH'.support, z ∈ (DHᶜ : Set (T : Set (Site 2))) := by
    intro z hz
    rw [hqH'supp, List.mem_map] at hz
    obtain ⟨u, _, hu⟩ := hz
    rw [← hu]; exact u.2
  
  set embT := SimpleGraph.Embedding.induce (G := G) (T : Set (Site 2)) with hembT
  set qG : G.Walk x y := qH'.map embT.toHom with hqG
  
  
  have hpHsupp : ∀ u : (T : Set (Site 2)), u ∈ pH.support ↔ (u : Site 2) ∈ p.support := by
    intro u
    rw [hpHsupp_eq, List.mem_attachWith]
  have hqGsupp : qG.support = qH'.support.map embT.toHom := by
    rw [hqG]; exact SimpleGraph.Walk.support_map (p := qH') (f := embT.toHom)
  have hqGoff : ∀ z ∈ qG.support, z ∈ arr_offPatchSet c := by
    intro z hz
    rw [hqGsupp, List.mem_map] at hz
    obtain ⟨u, huq, hu⟩ := hz
    have huD : u ∈ (DHᶜ : Set (T : Set (Site 2))) := hqH'avoid u huq
    have hzu : z = (u : Site 2) := by rw [← hu]; rfl
    rw [hzu]
    simp only [Set.mem_compl_iff, hDH, Set.mem_setOf_eq, not_and, not_not] at huD
    
    rw [arr_offPatchSet, Set.mem_setOf_eq]
    intro hpatchU
    
    
    
    
    by_cases huxy : (u : Site 2) = x
    · exact hx (huxy ▸ hpatchU)
    by_cases huy : (u : Site 2) = y
    · exact hy (huy ▸ hpatchU)
    · 
      
      have hunxH : u ≠ xH := fun h => huxy (Subtype.ext_iff.mp h)
      have hunyH : u ≠ yH := fun h => huy (Subtype.ext_iff.mp h)
      
      obtain ⟨n, hgvn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp huq
      have hn0 : n ≠ 0 := fun h => hunxH (by rw [h, Walk.getVert_zero] at hgvn; exact hgvn.symm)
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hltn : n - 1 < qH'.length := by
        have hnlen : n ≠ qH'.length := fun h => hunyH (by
          rw [h, Walk.getVert_length] at hgvn; exact hgvn.symm)
        lia
      have hadjn := qH'.adj_getVert_succ hltn
      rw [Nat.sub_add_cancel hnpos, hgvn] at hadjn
      
      have hGadjn : G.Adj ((qH'.getVert (n-1) : (T : Set (Site 2))) : Site 2) (u : Site 2) := hadjn
      have huGsupp : (u : Site 2) ∈ G.support := ⟨_, hGadjn.symm⟩
      have huPsupp : (u : Site 2) ∈ p.support := hpatch (u : Site 2) hpatchU huGsupp
      have huPHsupp : u ∈ pH.support := (hpHsupp u).mpr huPsupp
      
      exact hunyH (huD huPHsupp hunxH)
  
  exact arc_reachable_induce_of_avoidWalk hx hy qG hqGoff


theorem arc_harc_of_patchContiguous (hpc : arc_PatchContiguous K c a₀) :
    ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c),
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
        ⟨f, hfc⟩ ⟨a₀, hpc.1⟩ := by
  intro f hfc hf
  obtain ⟨p, hp⟩ := hpc.2 f hfc hf
  exact arc_reachable_induce_of_avoidWalk hfc hpc.1 p hp


theorem arc_cycleReachable_of_contiguous
    (hpc : arc_PatchContiguous K c a₀) (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  cyc_reachable_of_arcReachable hpc.1 (arc_harc_of_patchContiguous hpc) hH

end BoundaryArc


theorem arc_attachPreservesCycle_of_contiguous_noPinch
    (hAC : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        ∃ a₀ : Site 2, arc_PatchContiguous K c a₀ ∧ arr_Hook K c)
    (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        cyc_NoPinch (↑(insert c K) : Set (Site 2))) :
    cyc_AttachPreservesCycle := by
  apply cyc_attachPreservesCycle_of_reachable_noPinch
  · intro K c hc hconn hhf hcyc hconn' hhf'
    obtain ⟨a₀, hpc, hH⟩ := hAC K c hc hconn hhf hcyc hconn' hhf'
    exact arc_cycleReachable_of_contiguous hpc hH
  · exact hII


theorem arc_boundaryConnResidue_of_contiguous_noPinch
    (hAC : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        ∃ a₀ : Site 2, arc_PatchContiguous K c a₀ ∧ arr_Hook K c)
    (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        cyc_NoPinch (↑(insert c K) : Set (Site 2)))
    (hrem : fbc_HasRemovableCell) :
    fbc_BoundaryConnResidue :=
  cyc_boundaryConnResidue_of_inputs
    (arc_attachPreservesCycle_of_contiguous_noPinch hAC hII) hrem


theorem arc_contig_singleton_stays_connected :
    ∃ (ha : (0 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4)))
      (hb : (2 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4))),
      ((cycleGraph 4).induce ({(1 : Fin 4)}ᶜ : Set (Fin 4))).Reachable ⟨0, ha⟩ ⟨2, hb⟩ := by
  classical
  have hcyc : (cycleGraph 4).IsCycles := by
    intro v _
    rw [cycleGraph_neighborSet (n := 2)]
    exact Set.ncard_pair (by fin_cases v <;> decide)
  have hva : (cycleGraph 4).Adj 1 0 := by rw [cycleGraph_adj']; decide
  have hvb : (cycleGraph 4).Adj 1 2 := by rw [cycleGraph_adj']; decide
  have ha : (0 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4)) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; decide
  have hb : (2 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4)) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; decide
  exact ⟨ha, hb, arc_reachable_induce_compl_singleton hcyc (by decide) hva hvb ha hb⟩


theorem arc_faithful_tromino :
    insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧
      fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  ⟨ats_insert_domino_eq_tromino, ats_tromino_boundaryReachable⟩

end Walls
end StatMech
