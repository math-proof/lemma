/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullReachSet gamma gamma' omega ⊆
      rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  intro z hz hExt
  exact hExt.1 hz

theorem rlc_twoChannelFullExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullExteriorSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_twoChannelFullExteriorSet gamma gamma' omega) hpExt⟩

theorem rlc_twoChannelFullFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega).Finite := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  apply (box_finite 2 R).subset
  intro z hzFill
  by_contra hzBox
  have hzExt : z ∈ exterior 2 R := by
    rw [exterior_eq_compl_box]
    exact hzBox
  have hzNotK : z ∈ Kᶜ := exterior_subset_compl K R hR hzExt
  have hzInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hzExt
  have hzComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
        hzInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
  exact hzFill ⟨hzNotK, hzComp⟩


theorem rlc_twoChannelFullFilledReachSet_subset_connectorRect {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  have hKRect : K ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_twoChannelFullReachSet_subset_box gamma gamma' omega
  have promote {z q : Site 2}
      (hzNot : z ∈ Kᶜ) (hqExt : q ∈ exterior 2 R)
      (hzq : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, exterior_subset_compl K R hR hqExt⟩) :
      z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    let hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩).supp.Infinite :=
      exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
    have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
      (unique_infinite_component (by norm_num) K
        (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
          hqInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
    exact ⟨hzNot, (ConnectedComponent.sound hzq).trans hqComp⟩
  intro z hzFill
  rw [mem_rect]
  by_contra hzRect
  have hzCases : z 0 < -2 * n ∨ 2 * n < z 0 ∨
      z 1 < -n ∨ n < z 1 := by omega
  have hzNot : z ∈ Kᶜ := by
    intro hzK
    exact hzRect (by simpa [mem_rect] using hKRect hzK)
  rcases hzCases with hzLeft | hzRight | hzBottom | hzTop
  · let c : Int := z 0 - R - 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 0 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 0 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 0 + R + 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 0 ≤ c := by dsimp only [c]; omega
      have htBounds : z 0 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 - R - 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 1 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 1 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 + R + 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 1 ≤ c := by dsimp only [c]; omega
      have htBounds : z 1 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))

theorem rlc_twoChannelFull_walk_first_exit_set
    (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (a b : Site 2) (p : (hypercubicLattice 2).Walk x a),
      (hypercubicLattice 2).Adj a b ∧
        (∀ z ∈ p.support, z ∈ A) ∧ b ∉ A := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · obtain ⟨u, v, q, huv, hq, hv⟩ := ih hb hy
        refine ⟨u, v, Walk.cons hab q, huv, ?_, hv⟩
        simp only [SimpleGraph.Walk.support_cons, List.forall_mem_cons]
        exact ⟨hx, hq⟩
      · exact ⟨a, b, Walk.nil, hab, by simpa, hb⟩


theorem rlc_twoChannelFullFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    ∃ z : Site 2,
      ∃ hz : z ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_twoChannelFullReachSet_subset_filled
            gamma gamma' omega hz⟩ := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_twoChannelFull_walk_first_exit_set A w huA hkNotA
  have haA : a ∈ A := hqA a q.end_mem_support
  obtain ⟨haNotK, hua⟩ := haA
  have hbK : b ∈ K := by
    by_contra hbNotK
    have habK : ((hypercubicLattice 2).induce Kᶜ).Adj
        ⟨a, haNotK⟩ ⟨b, hbNotK⟩ := hab
    exact hbNotA ⟨hbNotK, hua.trans habK.reachable⟩
  have hAinH : A ⊆ H := by
    intro z hzA hzExt
    obtain ⟨hzNotK, huz⟩ := hzA
    obtain ⟨_hzNotK', hzComp⟩ := hzExt
    have huComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨u, huK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩

theorem rlc_twoChannelFullFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_twoChannelFullFilledReachSet_reaches_reachSet gamma gamma' omega hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_twoChannelFullFilledReachSet_reaches_reachSet gamma gamma' omega hv
  have hmiddle := (rlc_twoChannelFullReachSet_reachable
    gamma gamma' omega hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_twoChannelFullFilledReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_twoChannelFullFilledReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h

theorem rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullExteriorSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_twoChannelFullFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_twoChannelFullFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_twoChannelFullExteriorSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h


theorem rlc_twoChannelFullFilledReachSet_faceBoundaryConnected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FaceBoundaryConnected
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
      (phb_boundarySupport
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
        (rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega)) := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let hH := rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_twoChannelFullReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_twoChannelFullFilledReachSet_reachable_in_barrier
      gamma gamma' omega ha hb
  · intro a b ha hb
    apply rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier
      gamma gamma' omega
    · simpa [H, rlc_twoChannelFullFilledReachSet] using ha
    · simpa [H, rlc_twoChannelFullFilledReachSet] using hb


theorem rlc_twoChannelFullFilledBoundary_inside_mem_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {p q : Site 2}
    (hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hq : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  by_contra hpK
  have hqExt : q ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    simpa [rlc_twoChannelFullFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩

theorem rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hq : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
      hpq.2.mp hp
    have hpK := rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hp hq hpq.1
    have hqK : q ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
      intro hqK
      exact hq (rlc_twoChannelFullReachSet_subset_filled
        gamma gamma' omega hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hq hp hpq.1.symm
    have hpK : p ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
      intro hpK
      exact hp (rlc_twoChannelFullReachSet_subset_filled
        gamma gamma' omega hpK)
    simp [hpK, hqK]


theorem rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤
      faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach :=
    rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet
      gamma gamma' omega hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2


theorem rlc_twoChannelFullFilledBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) :=
  (rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    gamma gamma' omega).trans
      (rlc_twoChannelFullBoundary_le_openFaceDual gamma gamma' omega)


theorem rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices gamma'.1) :
    z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
  classical
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  let a : Site 2 := gamma'.1.1
  have haPath : a ∈ rlc_pathVertices gamma'.1 :=
    rlc_path_start_mem_vertices gamma'.1
  have haNot : a ∈ Kᶜ :=
    rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
      gamma gamma' omega hno haPath
  have ha0 : a 0 = -2 * n := gamma'.1.1.2.2
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hposition.right_axis_strict
    omega
  let c : Int := -2 * n - R - 1
  let q : Site 2 := ![c, a 1]
  have hqExt : q ∈ exterior 2 R := by
    refine ⟨0, ?_⟩
    simp [q, c]
    omega
  have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
  let W := rlc_ambientCrossingWalk gamma'.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).2
      hzPath
  let wTrace : (hypercubicLattice 2).Walk z a :=
    (W.takeUntil z hzW).reverse
  have haEq : a = ![-2 * n, a 1] := by
    ext i
    fin_cases i <;> simp [ha0]
  let wRay : (hypercubicLattice 2).Walk a q :=
    (sw_horizSeg (a 1) (-2 * n) c).copy haEq.symm rfl
  let w := wTrace.append wRay
  have hwNot : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    dsimp only [w] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvTrace | hvRay
    · have hvW : v ∈ W.support := by
        dsimp only [wTrace] at hvTrace
        have hvTake : v ∈ (W.takeUntil z hzW).support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
            using hvTrace
        exact W.support_takeUntil_subset_support hzW hvTake
      have hvPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 v).1 hvW
      exact rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
        gamma gamma' omega hno hvPath
    · change v ∈ ((sw_horizSeg (a 1) (-2 * n) c).copy _ _).support at hvRay
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvRay
      obtain ⟨t, ht, rfl⟩ := hvRay
      rw [Set.mem_uIcc] at ht
      have htLe : t ≤ -2 * n := by
        rcases ht with ht | ht <;> dsimp only [c] at ht <;> omega
      by_cases hteq : t = -2 * n
      · subst t
        rw [← haEq]
        exact haNot
      · intro htK
        have htRect := rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega htK
        rw [mem_rect] at htRect
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htRect
        omega
  have hzNot : z ∈ Kᶜ := hwNot z w.start_mem_support
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨z, hzNot⟩ ⟨q, hqNot⟩ := ⟨w.induce Kᶜ hwNot⟩
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨q, hqNot⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨q, hqNot⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
        hqInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
  exact ⟨hzNot, (ConnectedComponent.sound hreach).trans hqComp⟩


end
end StatMech.Universality
