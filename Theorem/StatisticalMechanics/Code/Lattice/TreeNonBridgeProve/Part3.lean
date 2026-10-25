/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNonBridgeProve.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {V : Type*}


theorem tnbp_neighbours_to_ref {c : Site 2} {B : Set (Site 2)} (h : tnbp_RingClear c B) :
    (ffc_offSupportLattice (insert c B)).Reachable ![c 0 - 1, c 1] ![c 0 + 1, c 1] ∧
      (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 + 1] ![c 0 + 1, c 1] ∧
      (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 - 1] ![c 0 + 1, c 1] := by
  obtain ⟨hE, hW, hN, hS, hNE, hNW, hSE, hSW⟩ := h
  set B' := insert c B
  set cx := c 0; set cy := c 1
  have rE_NE : (ffc_offSupportLattice B').Reachable ![cx + 1, cy] ![cx + 1, cy + 1] :=
    tnbp_step_reachable B' (vadj_step (cx + 1) cy) hE hNE
  have rNE_N : (ffc_offSupportLattice B').Reachable ![cx + 1, cy + 1] ![cx, cy + 1] :=
    tnbp_step_reachable B' (hadj_step cx (cy + 1)).symm hNE hN
  have rN_NW : (ffc_offSupportLattice B').Reachable ![cx, cy + 1] ![cx - 1, cy + 1] := by
    have := hadj_step (cx - 1) (cy + 1); simp only [show cx - 1 + 1 = cx by ring] at this
    exact tnbp_step_reachable B' this.symm hN hNW
  have rNW_W : (ffc_offSupportLattice B').Reachable ![cx - 1, cy + 1] ![cx - 1, cy] :=
    tnbp_step_reachable B' (vadj_step (cx - 1) cy).symm hNW hW
  have rS_SE : (ffc_offSupportLattice B').Reachable ![cx, cy - 1] ![cx + 1, cy - 1] :=
    tnbp_step_reachable B' (hadj_step cx (cy - 1)) hS hSE
  have rSE_E : (ffc_offSupportLattice B').Reachable ![cx + 1, cy - 1] ![cx + 1, cy] := by
    have := vadj_step (cx + 1) (cy - 1); simp only [show cy - 1 + 1 = cy by ring] at this
    exact tnbp_step_reachable B' this hSE hE
  refine ⟨?_, ?_, ?_⟩
  · exact (rNW_W.symm.trans rN_NW.symm).trans (rNE_N.symm.trans rE_NE.symm)
  · exact rNE_N.symm.trans rE_NE.symm
  · exact rS_SE.trans rSE_E


theorem tnbp_neighbours_connected_of_ringClear {c : Site 2} {B : Set (Site 2)}
    (h : tnbp_RingClear c B) : tnbp_RingConnected c B := by
  obtain ⟨rW, rN, rS⟩ := tnbp_neighbours_to_ref h
  
  have toRef : ∀ p : Site 2, (hypercubicLattice 2).Adj c p →
      (ffc_offSupportLattice (insert c B)).Reachable p ![c 0 + 1, c 1] := by
    intro p hp
    rcases tnbp_neighbour_cases hp with rfl | rfl | rfl | rfl
    · exact Reachable.refl _
    · exact rW
    · exact rN
    · exact rS
  intro p q hcp hcq
  exact (toRef p hcp.1).trans (toRef q hcq.1).symm


theorem tnbp_exterior_notMem {B' : Set (Site 2)} {R : ℕ} (hB : B' ⊆ box 2 R) {e : Site 2}
    (he : e ∈ exterior 2 R) : e ∉ B' := by
  rw [exterior_eq_compl_box] at he
  exact fun h => he (hB h)


theorem tnbp_reachesExterior_insert_of_ringConnected {B : Set (Site 2)} {R : ℕ} {c : Site 2}
    (hbase : arcxc_ReachesExterior B R) (hc : c ∈ box 2 R) (hring : tnbp_RingConnected c B) :
    arcxc_ReachesExterior (insert c B) R := by
  obtain ⟨hBsub, hreach⟩ := hbase
  have hsub : insert c B ⊆ box 2 R := Set.insert_subset hc hBsub
  refine ⟨hsub, ?_⟩
  intro x hx
  
  have hxB : x ∉ B := fun h => hx (Set.mem_insert_of_mem c h)
  have hxc : x ≠ c := fun h => hx (h ▸ Set.mem_insert c B)
  
  obtain ⟨e, p, hp, heExt⟩ := hreach x hxB
  
  have heBox : e ∉ box 2 R := by rw [exterior_eq_compl_box] at heExt; exact heExt
  have hec : e ≠ c := fun h => heBox (h.symm ▸ hc)
  
  have hxe_B : (ffc_offSupportLattice B).Reachable x e :=
    (ffc_reachable_iff_offSupportWalk hxB).mpr ⟨p, hp⟩
  have hxe_ins : (ffc_offSupportLattice (insert c B)).Reachable x e :=
    tnbp_reachable_insert_of_ringConnected hring hxc hec hxe_B
  obtain ⟨p', hp'⟩ := (ffc_reachable_iff_offSupportWalk hx).mp hxe_ins
  exact ⟨e, p', hp', heExt⟩


theorem tnbp_empty_reachesExterior (R : ℕ) : arcxc_ReachesExterior (∅ : Set (Site 2)) R := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro x _
  exact arcxc_reachesExterior_of_rowClear (fun t _ => Set.notMem_empty _)


end Lattice
end StatMech
