/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jei_sym2_mem_finite (e : Sym2 (Site 2)) : {x : Site 2 | x ∈ e}.Finite := by
  induction e with
  | _ a b =>
    apply Set.Finite.subset ((Set.finite_singleton a).insert b)
    intro x hx
    rw [Set.mem_setOf_eq, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert _ _


theorem jei_support_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    H.support.Finite := by
  classical
  apply Set.Finite.subset
    (Set.Finite.biUnion hfin (fun e (_ : e ∈ H.edgeSet) => jei_sym2_mem_finite e))
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  rw [Set.mem_iUnion₂]
  exact ⟨s(v, w), by rwa [SimpleGraph.mem_edgeSet], Sym2.mem_mk_left v w⟩


theorem jei_exterior_dual_edge_not_deleted (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2} (hf : f ∉ box 2 R) :
    crossEdge.symm s(f, g) ∉ H.edgeSet := by
  intro hmem
  have hsymm : crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
    simp [crossEdge, sym2Congr]
  rw [hsymm, SimpleGraph.mem_edgeSet] at hmem
  have hsupp : rot90Inv f ∈ H.support := ⟨rot90Inv g, hmem⟩
  have hrf : rot90Inv f ∈ box 2 R := hR _ hsupp
  have hf_eq : f = rot90Fun (rot90Inv f) := by
    have := rot90Equiv.right_inv f
    simpa [rot90Equiv] using this.symm
  exact hf (hf_eq ▸ rot90Fun_mem_box R hrf)


theorem jei_regionGraph_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2}
    (hf : f ∉ box 2 R) (hadj : (hypercubicLattice 2).Adj f g) :
    (regionGraph H).Adj f g :=
  ⟨hadj, jei_exterior_dual_edge_not_deleted H R hR hf⟩


theorem jei_regionComponents_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    Finite (regionGraph H).ConnectedComponent := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box H.support (jei_support_finite H hfin)
  set RG := regionGraph H with hRG
  set S : Set (Site 2) := box 2 R ∪ {beacon 2 R} with hS
  have hSfin : S.Finite := (box_finite 2 R).union (Set.finite_singleton _)
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  have hExtMk : ∀ x : Site 2, x ∈ exterior 2 R →
      RG.connectedComponentMk x = RG.connectedComponentMk (beacon 2 R) := by
    intro x hx
    refine ConnectedComponent.sound ?_
    have hconn := box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext
    have hmap := hconn.map
      (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 R)) →g RG)
    · simpa using hmap
    · intro a b hab
      have haext : (a : Site 2) ∉ box 2 R := mem_box_compl_of_exterior a.2
      exact jei_regionGraph_adj_of_exterior H R (fun v hv => hR hv) haext hab
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 R
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hxbox
    refine ⟨beacon 2 R, Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 R) = c
    rw [← hExtMk x hxext]; exact hx


end Lattice
end StatMech
