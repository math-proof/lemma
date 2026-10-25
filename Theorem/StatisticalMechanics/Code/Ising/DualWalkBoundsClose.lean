/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Equivalence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


theorem closedDualWalkParity_to_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    DualWalkBoundsRegion Gp Gd ψ := by
  intro w W
  
  
  set δ : Finset (Sym2 V) := (W.edges.toFinset).image ψ.symm with hδdef
  have hev : EvenOnCycles Gp δ := hlink W
  have hδsub : δ ⊆ Gp.edgeFinset := by
    intro e he
    rw [hδdef, Finset.mem_image] at he
    obtain ⟨g, hg, rfl⟩ := he
    have hgd : g ∈ Gd.edgeFinset := by
      rw [List.mem_toFinset] at hg
      rw [SimpleGraph.mem_edgeFinset]
      exact W.edges_subset_edgeSet hg
    exact hsymm g hgd
  
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  set S : ConfigSpace V := parityConfig Gp δ hG v₀ with hSdef
  refine ⟨S, ?_⟩
  intro u v huv
  
  have hcut : cutEdges Gp S = δ := cutEdges_parityConfig hev hG v₀ hδsub
  
  
  
  rw [← hcut]
  exact mem_cutEdges_iff Gp _ huv


theorem dualWalkBoundsRegion_iff_closedDualWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset) :
    DualWalkBoundsRegion Gp Gd ψ ↔ ClosedDualWalkParity Gp Gd ψ :=
  ⟨fun hreg => closedDualWalkParity_of_boundsRegion ψ hreg,
   fun hlink => closedDualWalkParity_to_boundsRegion hG ψ hsymm hlink⟩

end Equivalence


section LatticeRealisation

open StatMech.Lattice


theorem crossEdge_pullback_iff {Gd : SimpleGraph (Site 2)} {w : Site 2}
    (W : Gd.Walk w w) (u v : Site 2) :
    s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ crossEdge s(u, v) ∈ W.edges := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, hgeq⟩
    rw [List.mem_toFinset] at hg
    
    have : g = crossEdge s(u, v) := by rw [← hgeq, Equiv.apply_symm_apply]
    rw [this] at hg; exact hg
  · intro he
    exact ⟨crossEdge s(u, v), List.mem_toFinset.mpr he, crossEdge.symm_apply_apply _⟩


theorem latticeSide_boundsRegion_of_pullback_eq_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (S : Set (Site 2)) {w : Site 2}
    (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
    ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) :=
  ⟨latticeSide S, fun h => latticeSide_isRegion_of_pullback_eq_bdEdge crossEdge S W (fun h' => hpull h') h⟩


end LatticeRealisation
end Ising
end StatMech
