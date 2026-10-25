/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean -/

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
import Def.StatisticalMechanics.Code.Walls.fbcconnected
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem fbc_boundaryReachable_of_faceBoundaryConnected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T) :
    fbc_BoundaryReachable K := by
  intro f g hf hg
  have hfT : f ∈ (T : Set (Site 2)) := hsupp hf
  have hgT : g ∈ (T : Set (Site 2)) := hsupp hg
  
  have hr := (hconn.preconnected ⟨f, hfT⟩ ⟨g, hgT⟩)
  obtain ⟨p⟩ := hr
  
  refine ⟨(p.map (SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom)⟩


theorem fbc_support_nonempty {K : Finset (Site 2)} (hne : K.Nonempty) :
    ((faceBoundaryGraph (↑K : Set (Site 2))).support).Nonempty := by
  classical
  
  obtain ⟨x, hxK, hxmax⟩ := K.exists_max_image (fun p => p 0) hne
  
  have hright : (![x 0 + 1, x 1] : Site 2) ∉ (↑K : Set (Site 2)) := by
    intro hmem
    rw [Finset.mem_coe] at hmem
    have := hxmax _ hmem
    simp only [Matrix.cons_val_zero] at this
    omega
  have hxeq : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  
  
  
  
  have hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj ![x 0, x 1 - 1] ![x 0, x 1] := by
    rw [faceBoundaryGraph_adj]
    refine ⟨?_, ?_⟩
    · have := latAdj_top (x 0) (x 1 - 1); rwa [show x 1 - 1 + 1 = x 1 from by ring] at this
    · have h := sharedPrimalEdge_top (x 0) (x 1 - 1)
      rw [show x 1 - 1 + 1 = x 1 from by ring] at h
      rw [h]; unfold faceCorner01 faceCorner11
      rw [show x 1 - 1 + 1 = x 1 from by ring]
      
      rw [bdEdge_mk]
      constructor
      · intro _; exact hright
      · intro _; rw [Finset.mem_coe, ← hxeq]; exact hxK
  exact ⟨_, hadj.symm.mem_support_left⟩


theorem fbc_faceBoundaryConnected_false_of_isolated {K : Set (Site 2)} {T : Finset (Site 2)}
    {w : Site 2} (hwT : w ∈ T) (hiso : w ∉ (faceBoundaryGraph K).support)
    {s : Site 2} (hsT : s ∈ T) (hs : s ∈ (faceBoundaryGraph K).support) (hws : w ≠ s) :
    ¬ FaceBoundaryConnected K T := by
  intro hconn
  
  
  
  have hr := hconn.preconnected ⟨w, by exact_mod_cast hwT⟩ ⟨s, by exact_mod_cast hsT⟩
  obtain ⟨p⟩ := hr
  cases p with
  | nil =>
    
    exact hws rfl
  | cons hab q =>
    
    exact hiso ((SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom.map_adj hab).mem_support_left


theorem fbc_boundaryReachable_singleton :
    fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected


theorem fbc_card_one_eq_singleton {K : Finset (Site 2)} (hconn : IsConnectedCluster K)
    (hcard : K.card = 1) : K = {origin 2} := by
  obtain ⟨ho, _⟩ := hconn
  rw [Finset.card_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  rw [ha] at ho ⊢
  rw [Finset.mem_singleton] at ho
  rw [ho]


theorem fbc_boundaryReachable_of_inputs (hattach : fbc_AttachStep) (hrem : fbc_HasRemovableCell)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
    fbc_BoundaryReachable (↑K : Set (Site 2)) := by
  
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    
    have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
    have hpos : 1 ≤ K.card := Finset.card_pos.mpr hne
    rcases Nat.lt_or_ge K.card 2 with h1 | h2
    · 
      have hc1 : K.card = 1 := by omega
      rw [fbc_card_one_eq_singleton hconn hc1]
      exact fbc_boundaryReachable_singleton
    · 
      obtain ⟨c, hcK, _hcorigin, hconn', hhf'⟩ := hrem K h2 hconn hhf
      
      have hcard' : (K.erase c).card < K.card := by
        rw [Finset.card_erase_of_mem hcK]; omega
      
      have hreach' : fbc_BoundaryReachable (↑(K.erase c) : Set (Site 2)) :=
        ih (K.erase c).card hcard' (K.erase c) hconn' hhf' rfl
      
      have hins : insert c (K.erase c) = K := Finset.insert_erase hcK
      have hcnotin : c ∉ K.erase c := Finset.notMem_erase c K
      have := hattach (K.erase c) c hcnotin hconn' hhf' hreach'
        (by rw [hins]; exact hconn) (by rw [hins]; exact hhf)
      rwa [hins] at this


end Walls
end StatMech
