/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_whb_exterior_in_outerRegion (P : PlanarZ2Subgraph) {x : Site 2}
    (hx : x ∈ exterior 2 (outerBoxRadius P + 1)) :
    (whb_faceRegion (imageGraph P)).connectedComponentMk x = jfc_whb_outerRegion P := by
  set R := outerBoxRadius P with hR
  set RG := whb_faceRegion (imageGraph P) with hRG
  have hb_ext : beacon 2 (R + 1) ∈ exterior 2 (R + 1) := beacon_mem_exterior (R + 1) (by omega)
  refine ConnectedComponent.sound ?_
  have hconn := box_exterior_connected (R + 1) (by omega) x (beacon 2 (R + 1)) hx hb_ext
  have hmap := hconn.map
    (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 (R + 1))) →g RG)
  · simpa using hmap
  · intro a b hab
    exact jfc_whb_adj_of_exterior (imageGraph P) R (jfc_imageGraph_support_box P) a.2 hab


theorem jfc_whb_outerRegion_infinite (P : PlanarZ2Subgraph) :
    (jfc_whb_outerRegion P).supp.Infinite := by
  set R := outerBoxRadius P with hR
  have : Infinite ↥(exterior 2 (R + 1)) := (exterior_infinite (R + 1) (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 (R + 1)) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact jfc_whb_exterior_in_outerRegion P w.2


theorem jfc_whb_infiniteComponent_meets_exterior (P : PlanarZ2Subgraph)
    {C : (whb_faceRegion (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P + 1) := by
  set R := outerBoxRadius P with hR
  by_contra hcon
  push Not at hcon
  have hsubbox : C.supp ⊆ box 2 (R + 1) := by
    intro v hv
    have hvnotext : v ∉ exterior 2 (R + 1) := hcon v hv
    rw [exterior_eq_compl_box, Set.mem_compl_iff, not_not] at hvnotext
    exact hvnotext
  exact hC ((box_finite 2 (R + 1)).subset hsubbox)


theorem jfc_whb_unique_infinite_component (P : PlanarZ2Subgraph) :
    ∃! C : (whb_faceRegion (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  refine ⟨jfc_whb_outerRegion P, jfc_whb_outerRegion_infinite P, ?_⟩
  intro C hCinf
  obtain ⟨x, hx_supp, hx_ext⟩ := jfc_whb_infiniteComponent_meets_exterior P hCinf
  have h1 : (whb_faceRegion (imageGraph P)).connectedComponentMk x = C :=
    (C.mem_supp_iff x).mp hx_supp
  have h2 : (whb_faceRegion (imageGraph P)).connectedComponentMk x = jfc_whb_outerRegion P :=
    jfc_whb_exterior_in_outerRegion P hx_ext
  rw [← h1, h2]


theorem jfc_whb_bounded_iff_ne_outer (P : PlanarZ2Subgraph)
    (C : (whb_faceRegion (imageGraph P)).ConnectedComponent) :
    C.supp.Finite ↔ C ≠ jfc_whb_outerRegion P := by
  constructor
  · intro hfin hcon
    rw [hcon] at hfin
    exact (jfc_whb_outerRegion_infinite P) hfin
  · intro hne
    by_contra hinf
    rw [Set.not_finite] at hinf
    exact hne ((jfc_whb_unique_infinite_component P).unique hinf (jfc_whb_outerRegion_infinite P))


theorem jfc_whb_bounded_add_one_eq_card (P : PlanarZ2Subgraph) :
    whc_faithfulRegionCount P + 1 =
      Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P)
      (Set.toFinite (imageGraph P).edgeSet)
  unfold whc_faithfulRegionCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight (jfc_whb_bounded_iff_ne_outer P)),
    card_subtype_ne_add_one (jfc_whb_outerRegion P)]


theorem jfc_whb_total_count_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jfc_whb_count_of_sync P hsync P.G le_rfl
  rwa [jei_pushGraph_G P] at h


theorem jfc_whb_faithfulRegionCount_eq_nullity_of_sync (P : PlanarZ2Subgraph)
    (hsync : jfc_WhbSync P) : whc_faithfulRegionCount P = nullity P.G := by
  have htot := jfc_whb_total_count_of_sync P hsync
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega


theorem jfc_faithfulDiscreteJordan_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jfc_whb_faithfulRegionCount_eq_nullity_of_sync P hsync
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩


theorem jfc_pushGraph_le_lattice (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G) :
    jei_pushGraph P K ≤ hypercubicLattice 2 := by
  rintro a b ⟨x, y, hadj, rfl, rfl⟩
  exact P.isSub (hKle hadj)


end Lattice
end StatMech
