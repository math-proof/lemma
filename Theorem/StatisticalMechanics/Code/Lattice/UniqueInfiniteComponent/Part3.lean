/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

variable {d : ℕ}


theorem beacon_natAbs (R : ℕ) (k : Fin d) : ((beacon d R) k).natAbs = R + 1 := by
  show ((R : ℤ) + 1).natAbs = R + 1
  rw [Int.natAbs_eq_iff]; left; push_cast; ring

theorem beacon_mem_exterior (R : ℕ) (hd : 1 ≤ d) : beacon d R ∈ exterior d R := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  rw [beacon_natAbs]; omega


theorem exterior_reachable_beacon (R : ℕ) (hd : 2 ≤ d) (p : Site d)
    (hp : p ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hp⟩
      ⟨beacon d R, beacon_mem_exterior R (by omega)⟩ := by
  classical
  obtain ⟨i0, hi0⟩ := hp
  
  set T := Finset.univ \ {i0} with hT
  have hi0T : i0 ∉ T := by simp [hT]
  have hp' : p ∈ exterior d R := ⟨i0, hi0⟩
  
  set p1 := setOn p T ((R : ℤ) + 1) with hp1
  have hp1_i0 : p1 i0 = p i0 := setOn_notMem p T _ hi0T
  have hp1_ext : p1 ∈ exterior d R := ⟨i0, by rw [hp1_i0]; exact hi0⟩
  have phase1 := exterior_reachable_setOn R p i0 hi0 T hi0T hp' hp1_ext
  
  
  have hcard : 1 < Fintype.card (Fin d) := by simpa using hd
  obtain ⟨i1, hi1ne⟩ := Fintype.exists_ne_of_one_lt_card hcard i0
  have hi1T : i1 ∈ T := by simp [hT, hi1ne]
  have hp1_i1 : p1 i1 = (R : ℤ) + 1 := by simp [hp1, setOn, hi1T]
  
  have hupd_beacon : Function.update p1 i0 ((R : ℤ) + 1) = beacon d R := by
    funext k
    by_cases hk : k = i0
    · subst hk; simp [beacon]
    · rw [Function.update_of_ne hk]
      
      have hkT : k ∈ T := by simp [hT, hk]
      simp [hp1, setOn, hkT, beacon]
  have hbeacon_ext : Function.update p1 i0 ((R : ℤ) + 1) ∈ exterior d R := by
    rw [hupd_beacon]; exact beacon_mem_exterior R (by omega)
  have hseg2 : ∀ z : ℤ, (min (p1 i0) ((R : ℤ) + 1) ≤ z ∧ z ≤ max (p1 i0) ((R : ℤ) + 1)) →
      Function.update p1 i0 z ∈ exterior d R := by
    intro z _
    refine ⟨i1, ?_⟩
    rw [Function.update_of_ne hi1ne, hp1_i1]
    have : ((R : ℤ) + 1).natAbs = R + 1 := by rw [Int.natAbs_eq_iff]; left; push_cast; ring
    rw [this]; omega
  have phase2 := segment_gen (exterior d R) i0 p1 ((R : ℤ) + 1) hp1_ext hbeacon_ext hseg2
  have hchain := phase1.trans phase2
  
  have heq : (⟨Function.update p1 i0 ((R : ℤ) + 1), hbeacon_ext⟩ : exterior d R)
      = ⟨beacon d R, beacon_mem_exterior R (by omega)⟩ := Subtype.ext hupd_beacon
  rw [heq] at hchain
  exact hchain


theorem box_exterior_connected (R : ℕ) (hd : 2 ≤ d) (x y : Site d)
    (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  (exterior_reachable_beacon R hd x hx).trans (exterior_reachable_beacon R hd y hy).symm


theorem exterior_infinite (R : ℕ) (hd : 2 ≤ d) : (exterior d R).Infinite := by
  have hcard : 1 < Fintype.card (Fin d) := by simpa using hd
  obtain ⟨i1, _⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, by omega⟩
  obtain ⟨i0, hi0ne⟩ := Fintype.exists_ne_of_one_lt_card hcard i1
  set b : Site d := beacon d R with hb
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => Function.update b i1 m) ?_ ?_
  · intro a c hac
    have := congrFun hac i1
    simpa using this
  · intro m
    refine ⟨i0, ?_⟩
    show R < (Function.update b i1 m i0).natAbs
    rw [Function.update_of_ne hi0ne, hb, beacon_natAbs]
    omega


theorem finite_subset_box (F : Set (Site d)) (hF : F.Finite) : ∃ R : ℕ, F ⊆ box d R := by
  classical
  set g : Site d → ℕ := fun x => Finset.univ.sup (fun i => (x i).natAbs) with hg
  refine ⟨hF.toFinset.sup g, ?_⟩
  intro x hx i
  have hxF : x ∈ hF.toFinset := by rwa [Set.Finite.mem_toFinset]
  have h1 : (x i).natAbs ≤ g x := Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  have h2 : g x ≤ hF.toFinset.sup g := Finset.le_sup hxF
  exact h1.trans h2


theorem exterior_subset_compl (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R) :
    exterior d R ⊆ Fᶜ := by
  rw [exterior_eq_compl_box]
  exact Set.compl_subset_compl.mpr hF


theorem exterior_reachable_compl (F : Set (Site d)) (R : ℕ) (hd : 2 ≤ d)
    (hsub : exterior d R ⊆ Fᶜ) (x y : Site d)
    (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).Reachable ⟨x, hsub hx⟩ ⟨y, hsub hy⟩ := by
  have h := box_exterior_connected R hd x y hx hy
  simpa using h.map ((hypercubicLattice d).induceHomOfLE hsub).toHom


theorem unique_infinite_component (hd : 2 ≤ d) (F : Set (Site d)) (hF : F.Finite) :
    ∃! C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent, C.supp.Infinite := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box F hF
  set G := (hypercubicLattice d).induce Fᶜ with hG
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hR
  have hb_ext : beacon d R ∈ exterior d R := beacon_mem_exterior R (by omega)
  set v0 : ↥Fᶜ := ⟨beacon d R, hsub hb_ext⟩ with hv0
  set C0 := G.connectedComponentMk v0 with hC0
  
  have hExtComp : ∀ (x : Site d) (hx : x ∈ exterior d R),
      G.connectedComponentMk ⟨x, hsub hx⟩ = C0 := by
    intro x hx
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R hd hsub x (beacon d R) hx hb_ext)
  
  have hC0_inf : C0.supp.Infinite := by
    have : Infinite ↥(exterior d R) := (exterior_infinite R hd).to_subtype
    refine Set.infinite_of_injective_forall_mem
      (f := fun w : ↥(exterior d R) => (⟨(w : Site d), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
    · intro a b hab
      exact Subtype.ext (by simpa using congrArg Subtype.val hab)
    · intro w
      rw [ConnectedComponent.mem_supp_iff]
      exact hExtComp (w : Site d) w.2
  refine ⟨C0, hC0_inf, ?_⟩
  
  intro C hCinf
  obtain ⟨v, hv_supp, hv_ext⟩ : ∃ v : ↥Fᶜ, v ∈ C.supp ∧ (v : Site d) ∈ exterior d R := by
    by_contra hcon
    have hcon' : ∀ v ∈ C.supp, (v : Site d) ∉ exterior d R := by
      intro v hv hve; exact hcon ⟨v, hv, hve⟩
    have hsubbox : C.supp ⊆ (Subtype.val ⁻¹' (box d R)) := by
      intro v hv
      have hvb : (v : Site d) ∈ (exterior d R)ᶜ := hcon' v hv
      rw [exterior_eq_compl_box, compl_compl] at hvb
      exact hvb
    have hfin : (Subtype.val ⁻¹' (box d R) : Set ↥Fᶜ).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn (box_finite d R)
    exact hCinf (hfin.subset hsubbox)
  have h1 : G.connectedComponentMk v = C := (C.mem_supp_iff v).mp hv_supp
  have h2 : G.connectedComponentMk v = C0 := hExtComp (v : Site d) hv_ext
  rw [← h1, h2]

end Lattice
end StatMech
