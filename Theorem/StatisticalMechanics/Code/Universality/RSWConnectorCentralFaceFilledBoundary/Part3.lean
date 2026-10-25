/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_connectorCentralFaceReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceReachSet gamma gamma' rho ⊆
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  intro z hz hExt
  exact hExt.1 hz

theorem rlc_connectorCentralFaceExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    hpExt⟩

theorem rlc_connectorCentralFaceFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho).Finite := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
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
      ⟨z, hzNotK⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
        hzInf
        (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
  exact hzFill ⟨hzNotK, hzComp⟩


theorem rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  have hKRect : K ⊆ rect (-2 * n) (2 * n) (-n) n := by
    rintro z ⟨hz, _⟩
    exact hz
  have promote {z q : Site 2}
      (hzNot : z ∈ Kᶜ) (hqExt : q ∈ exterior 2 R)
      (hzq : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, exterior_subset_compl K R hR hqExt⟩) :
      z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    let hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩).supp.Infinite :=
      exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
    have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩ =
          rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
      (unique_infinite_component (by norm_num) K
        (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
          hqInf
          (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
    exact ⟨hzNot, (ConnectedComponent.sound hzq).trans hqComp⟩
  intro z hzFill
  rw [mem_rect]
  by_contra hzRect
  have hzCases : z 0 < -2 * n ∨ 2 * n < z 0 ∨
      z 1 < -n ∨ n < z 1 := by
    omega
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
      intro t ht
      intro htK
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
      intro t ht
      intro htK
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
      intro t ht
      intro htK
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
      intro t ht
      intro htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 1 ≤ c := by dsimp only [c]; omega
      have htBounds : z 1 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))


theorem rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_connectorCentralFaceFilledReachSet,
            Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_connectorCentralFaceFilledReachSet,
            Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_connectorCentralFaceExteriorSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h

theorem rlc_centralFace_walk_first_exit_set
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


theorem rlc_connectorCentralFaceFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    ∃ z : Site 2,
      ∃ hz : z ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho,
      ((hypercubicLattice 2).induce
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_connectorCentralFaceReachSet_subset_filled
            gamma gamma' rho hz⟩ := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_centralFace_walk_first_exit_set A w huA hkNotA
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
        ⟨u, huK⟩ =
          rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩

theorem rlc_connectorCentralFaceFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_connectorCentralFaceFilledReachSet_reaches_reachSet
      gamma gamma' rho hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_connectorCentralFaceFilledReachSet_reaches_reachSet
      gamma gamma' rho hv
  have hmiddle := (rlc_connectorCentralFaceReachSet_reachable
    gamma gamma' rho hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_connectorCentralFaceReachSet_subset_filled
          gamma gamma' rho)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorCentralFaceFilledReachSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h


theorem rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FaceBoundaryConnected
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
      (phb_boundarySupport
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
        (rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho)) := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
      gamma gamma' rho ha hb
  · intro a b ha hb
    apply rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
      gamma gamma' rho
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using ha
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using hb


theorem rlc_connectorCentralFaceFilledBoundary_degree_eq_two
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).degree f = 2 := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryGraph_degree_eq_two_of_connected_complement
    H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier
      gamma gamma' rho ha hb
  · intro a b ha hb
    apply rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using ha
    · simpa [H, rlc_connectorCentralFaceFilledReachSet] using hb
  · exact hf


theorem rlc_connectorCentralFaceFilledBoundary_isCycles
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).IsCycles := by
  intro f hf
  have hfSupport : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support := by
    obtain ⟨g, hfg⟩ := hf
    exact hfg.mem_support_left
  rw [Set.ncard_eq_toFinset_card']
  exact rlc_connectorCentralFaceFilledBoundary_degree_eq_two
    gamma gamma' rho hfSupport


theorem rlc_isCycle_of_isCycles_isTrail
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {v : V} (c : G.Walk v v) (hcycles : G.IsCycles)
    (hcne : c ≠ .nil) (hcTrail : c.IsTrail) : c.IsCycle := by
  let p := c.cycleBypass
  have hpCycle : p.IsCycle := hcTrail.isCycle_cycleBypass hcne
  have hpStep {a b : V} (ha : a ∈ p.support) (hab : G.Adj a b) :
      s(a, b) ∈ p.edges := by
    have haVerts : a ∈ p.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using ha
    have habSub : p.toSubgraph.Adj a b :=
      (hpCycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
    exact p.adj_toSubgraph_iff_mem_edges.mp habSub
  have walk_subset {a b : V} (w : G.Walk a b)
      (ha : a ∈ p.support) :
      w.edges ⊆ p.edges ∧ b ∈ p.support := by
    induction w with
    | nil => exact ⟨by simp, ha⟩
    | @cons a b d hab w ih =>
        have habP : s(a, b) ∈ p.edges := hpStep ha hab
        have hb : b ∈ p.support :=
          p.snd_mem_support_of_mem_edges habP
        have hi := ih hb
        constructor
        · intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          exact he.elim (fun h => h ▸ habP) (fun h => hi.1 h)
        · exact hi.2
  have hcSubset : c.edges ⊆ p.edges :=
    (walk_subset c p.start_mem_support).1
  have hpSubset : p.edges ⊆ c.edges := by
    exact SimpleGraph.Walk.edges_cycleBypass_subset
  have hcp : c.edges.length ≤ p.edges.length := by
    rw [← List.toFinset_card_of_nodup hcTrail.edges_nodup,
      ← List.toFinset_card_of_nodup hpCycle.edges_nodup]
    exact Finset.card_le_card (by
      intro e he
      exact List.mem_toFinset.mpr (hcSubset (List.mem_toFinset.mp he)))
  have hpc : p.edges.length ≤ c.edges.length := by
    rw [← List.toFinset_card_of_nodup hpCycle.edges_nodup,
      ← List.toFinset_card_of_nodup hcTrail.edges_nodup]
    exact Finset.card_le_card (by
      intro e he
      exact List.mem_toFinset.mpr (hpSubset (List.mem_toFinset.mp he)))
  have hlength : p.length = c.length := by
    rw [← SimpleGraph.Walk.length_edges, ← SimpleGraph.Walk.length_edges]
    omega
  cases c with
  | nil => exact False.elim (hcne rfl)
  | @cons a b h hab w =>
      have hbypassLength : w.length ≤ w.bypass.length := by
        dsimp only [p, SimpleGraph.Walk.cycleBypass] at hlength
        simpa using hlength.ge
      have hbypass : w.bypass = w :=
        w.bypass_eq_self_of_length_le hbypassLength
      rw [SimpleGraph.Walk.isCycle_def]
      refine ⟨hcTrail, by simp, ?_⟩
      simpa [hbypass] using w.bypass_isPath.support_nodup


theorem rlc_connectorCentralFaceFilledBoundary_other_neighbor
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
    ∃ b : Site 2,
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧
      u ≠ b := by
  let G := faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  have hvSupport : v ∈ G.support := huv.mem_support_right
  have hdegree : G.degree v = 2 :=
    rlc_connectorCentralFaceFilledBoundary_degree_eq_two
      gamma gamma' rho hvSupport
  by_contra hnone
  push Not at hnone
  have hsub : G.neighborFinset v ⊆ {u} := by
    intro b hb
    simp only [Finset.mem_singleton]
    exact (hnone b (SimpleGraph.mem_neighborFinset G v b |>.mp hb)).symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree,
    hdegree] at hcard
  omega


theorem rlc_connectorCentralFaceFilledBoundary_existsUnique_other_neighbor
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
    ∃! b : Site 2,
      u ≠ b ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b := by
  exact (rlc_connectorCentralFaceFilledBoundary_isCycles
    gamma gamma' rho).existsUnique_ne_adj huv.symm


theorem rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hp : p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hq : q ∉ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  by_contra hpK
  have hqExt : q ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩

theorem rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · have hq : q ∉
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := hpq.2.mp hp
    have hpK := rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
      gamma gamma' rho hp hq hpq.1
    have hqK : q ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      intro hqK
      exact hq (rlc_connectorCentralFaceReachSet_subset_filled
        gamma gamma' rho hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet
      gamma gamma' rho hq hp hpq.1.symm
    have hpK : p ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      intro hpK
      exact hp (rlc_connectorCentralFaceReachSet_subset_filled
        gamma gamma' rho hpK)
    simp [hpK, hqK]


theorem rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ≤
      faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach :=
    rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet
      gamma gamma' rho hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2


theorem rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  have hfgReach : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g :=
    rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' rho hfg
  intro htrace
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfgReach.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfgReach.2
  rcases Finset.mem_union.mp htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 (hpq ▸ hright)
    have hpReach := rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hends.1
    have hqReach := rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hends.2
    exact (hpqBoundary.2.mp hpReach) hqReach
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 (hpq ▸ hleft)
    have hpNot := rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hends.1
    have hqNot := rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hends.2
    exact hpNot (hpqBoundary.2.mpr hqNot)


theorem rlc_connectorCentralFaceFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
        f g := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  have hconn :=
    rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
      gamma gamma' rho
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom


end
end StatMech.Universality
