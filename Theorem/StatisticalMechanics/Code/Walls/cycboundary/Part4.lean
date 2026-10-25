/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean -/

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
import Def.StatisticalMechanics.Code.Walls.cycboundary.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem cyc_attachReachable_of_preserves (hpres : cyc_AttachPreservesCycle)
    (K : Finset (Site 2)) (c : Site 2) (hc : c ∉ K)
    (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2)))
    (hcyc : cyc_BoundaryCycle (↑K : Set (Site 2)))
    (hconn' : IsConnectedCluster (insert c K))
    (hhf' : pc2_HoleFree (↑(insert c K) : Set (Site 2))) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  cyc_boundaryCycle_imp_reachable
    (hpres K c hc hconn hhf hcyc hconn' hhf')


theorem cyc_boundaryCycle_singleton :
    cyc_BoundaryCycle (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  refine ⟨fbc_boundaryReachable_singleton, fun f hf => ?_⟩
  
  have hf4 := support_singletonOrigin_subset hf
  rw [Finset.mem_coe] at hf4
  
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rw [hfeq, degree_faceBoundaryGraph]
  
  rcases singletonBoundarySupport_cases hf4 with rfl | rfl | rfl | rfl <;>
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01
    simp only [mem_singletonOrigin]
    norm_num


theorem cyc_boundaryCycle_of_inputs (hpres : cyc_AttachPreservesCycle) (hrem : fbc_HasRemovableCell)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
    cyc_BoundaryCycle (↑K : Set (Site 2)) := by
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
    have hpos : 1 ≤ K.card := Finset.card_pos.mpr hne
    rcases Nat.lt_or_ge K.card 2 with h1 | h2
    · have hc1 : K.card = 1 := by omega
      rw [fbc_card_one_eq_singleton hconn hc1]
      exact cyc_boundaryCycle_singleton
    · obtain ⟨c, hcK, _hcorigin, hconn', hhf'⟩ := hrem K h2 hconn hhf
      have hcard' : (K.erase c).card < K.card := by
        rw [Finset.card_erase_of_mem hcK]; omega
      have hcyc' : cyc_BoundaryCycle (↑(K.erase c) : Set (Site 2)) :=
        ih (K.erase c).card hcard' (K.erase c) hconn' hhf' rfl
      have hins : insert c (K.erase c) = K := Finset.insert_erase hcK
      have hcnotin : c ∉ K.erase c := Finset.notMem_erase c K
      have := hpres (K.erase c) c hcnotin hconn' hhf' hcyc'
        (by rw [hins]; exact hconn) (by rw [hins]; exact hhf)
      rwa [hins] at this


theorem cyc_boundaryConnResidue_of_inputs
    (hpres : cyc_AttachPreservesCycle) (hrem : fbc_HasRemovableCell) :
    fbc_BoundaryConnResidue :=
  fun K hconn hhf => cyc_boundaryCycle_imp_reachable
    (cyc_boundaryCycle_of_inputs hpres hrem K hconn hhf)


theorem cyc_attachPreservesCycle_of_reachable_noPinch
    (hI : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)))
    (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        cyc_NoPinch (↑(insert c K) : Set (Site 2))) :
    cyc_AttachPreservesCycle := by
  intro K c hc hconn hhf hcyc hconn' hhf'
  exact cyc_boundaryCycle_of_noPinch
    (hI K c hc hconn hhf hcyc hconn' hhf')
    (hII K c hc hconn hhf hcyc hconn' hhf')


theorem cyc_reachable_of_arr {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  arr_boundaryReachable_of_reroute_hook hR hH


theorem cyc_reachable_of_arcReachable {K : Finset (Site 2)} {c a₀ : Site 2}
    (ha₀ : a₀ ∈ arr_offPatchSet c)
    (harc : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c),
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
          ⟨f, hfc⟩ ⟨a₀, ha₀⟩)
    (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  arr_boundaryReachable_of_reroute_hook (arr_reRoute_of_induceReachable ha₀ harc) hH


end Walls
end StatMech
