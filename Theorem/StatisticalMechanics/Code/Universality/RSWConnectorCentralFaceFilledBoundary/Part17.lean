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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_connectorCentralFaceGoodBoundaryGraph_le {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := by
  intro f g hfg
  exact hfg.1

theorem RlcCentralFaceRetainedAnchoredBoundary.anchor_mem_goodBoundaryGraph
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj
      B.firstFace B.secondFace := by
  refine ⟨B.anchor_adj, ?_⟩
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' B.anchor_adj.1).2
      (B.anchor_reflected_mem_planar hfaith)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          N z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (![0, L.boundary.height + 1] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' ∨
      (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma' := by
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le
    gamma gamma' rho
  let p := q.mapLe hle
  obtain ⟨w, hwSupport, z, hzw, hzBarrier⟩ :=
    L.boundaryPrefix_to_outsideAxis_meetsBarrier hfaith p hN huNeg
      hreflected hkOutside
  rcases hwSupport z hzw with hzAnchor | hzOutside | ⟨f, hf, hzf⟩
  · exact Or.inr (Or.inl (by simpa [hzAnchor] using hzBarrier))
  · exact Or.inr (Or.inr (by simpa [hzOutside] using hzBarrier))
  · left
    have hfQ : f ∈ q.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hf
    refine ⟨f, ⟨q.takeUntil f hfQ⟩, ?_⟩
    rwa [hzf] at hzBarrier


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeAnchor_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {N : Site 2}
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2)) :
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
      L.boundary.firstFace N := by
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, L.boundary.height + 1] : Site 2),
          ![0, L.boundary.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hmem : rlc_dualReflect N ∈
      s(rlc_dualReflect L.boundary.firstFace,
        rlc_dualReflect L.boundary.secondFace) := by
    rw [htarget, hN]
    exact Sym2.mem_mk_left _ _
  rw [Sym2.mem_iff] at hmem
  rcases hmem with hmem | hmem
  · have hEq : N = L.boundary.firstFace :=
      rlc_dualReflect.injective hmem
    subst N
    exact Reachable.refl _
  · have hEq : N = L.boundary.secondFace :=
      rlc_dualReflect.injective hmem
    subst N
    exact (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable


theorem rlc_goodBoundary_reachable_dualReflect_mem_box_of_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x z : Site 2}
    (hx : rlc_dualReflect x ∈ rlc_connectorBox n)
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x z) :
    rlc_dualReflect z ∈ rlc_connectorBox n := by
  obtain ⟨w⟩ := hz
  induction w with
  | nil => exact hx
  | @cons u v t huv p ih =>
      apply ih
      have hplanar :=
        (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
          gamma gamma' huv.1.1).1 huv.2
      exact rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
        gamma gamma' hplanar (Sym2.mem_mk_right _ _)

theorem rlc_goodBoundary_reachable_dualReflect_mem_box
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    rlc_dualReflect z ∈ rlc_connectorBox n := by
  have hstart : rlc_dualReflect B.firstFace ∈ rlc_connectorBox n :=
    rlc_connectorCentralFacePlanarEdge_endpoints_mem_box gamma gamma'
      (B.anchor_reflected_mem_planar hfaith)
      (Sym2.mem_mk_left _ _)
  exact rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hstart hz


theorem rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ A : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, B.height + 1] : Site 2) ∧
        (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
          rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') := by
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, B.height + 1] : Site 2), ![0, B.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hzeroMem : (![0, B.height + 1] : Site 2) ∈
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) := by
    rw [htarget]
    exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hzeroMem
  obtain ⟨A, hfirstA, hAfirst, hAzero⟩ :
      ∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, B.height + 1] : Site 2) := by
    rcases hzeroMem with hfirst | hsecond
    · exact ⟨B.firstFace, Reachable.refl _, Reachable.refl _, hfirst.symm⟩
    · exact ⟨B.secondFace, hanchor.reachable,
        hanchor.reachable.symm, hsecond.symm⟩
  refine ⟨A, hfirstA, hAfirst, hAzero, ?_⟩
  by_cases hbarrier : (![0, B.height + 1] : Site 2) ∈
      rlc_connectorBarrier gamma gamma'
  · rcases (rlc_axis_mem_connectorBarrier_iff
      gamma gamma' (B.height + 1)).1 hbarrier with hright | hleft
    · have haxis := hfaith.right_axis_unique hright (by simp)
      have hheight := congrArg (fun z : Site 2 => z 1) haxis
      have hlower := B.height_lower
      simp at hheight
      omega
    · exact Or.inl (by simpa [hAzero] using hleft)
  · exact Or.inr (by simpa [hAzero] using hbarrier)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.axisAnchor_barrier_forces_reachable_left_contact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hbarrier : (![0, L.boundary.height + 1] : Site 2) ∈
      rlc_connectorBarrier gamma gamma') :
    ∃ A : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace A ∧
        rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 := by
  obtain ⟨A, hfirstA, _hAfirst, hAzero, hleft | hoff⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  · exact ⟨A, hfirstA, hleft⟩
  · exact False.elim (hoff (by simpa [hAzero] using hbarrier))


theorem rlc_faithful_axisOutside_barrier_classify {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hbarrier : (![0, k] : Site 2) ∈
      rlc_connectorBarrier gamma gamma') :
    (k ≤ (gamma.1.1 : Site 2) 1 →
      (![0, k] : Site 2) ∈ rlc_pathVertices gamma.1) ∧
    ((gamma'.1.2.1 : Site 2) 1 < k → False) := by
  have haxis := (rlc_axis_mem_connectorBarrier_iff gamma gamma' k).1 hbarrier
  constructor
  · intro hk
    rcases haxis with hright | hleft
    · exact hright
    · have heq := hfaith.left_axis_unique hleft (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      have horder := hfaith.axis_contacts_strict
      simp at heq1
      omega
  · intro hk
    rcases haxis with hright | hleft
    · have heq := hfaith.right_axis_unique hright (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      have horder := hfaith.axis_contacts_strict
      simp at heq1
      omega
    · have heq := hfaith.left_axis_unique hleft (by simp)
      have heq1 := congrArg (fun z : Site 2 => z 1) heq
      simp at heq1
      omega


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_contact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace A ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1) ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma.1 := by
  have hfirstN := L.negativeAnchor_reachable hfaith hN
  rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint
      hfaith q hN huNeg hreflected hkOutside with
    ⟨z, hNz, hzBarrier⟩ | hAnchor | hOutside
  · exact Or.inl ⟨z, hfirstN.trans hNz, hzBarrier⟩
  · exact Or.inr (Or.inl
      (L.axisAnchor_barrier_forces_reachable_left_contact
        hfaith hAnchor))
  · have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
      rw [Sym2.eq_iff] at hreflected
      rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
      · exact hv
      · have h0 := congrArg (fun z : Site 2 => z 0) hu
        have h0' : (rlc_dualReflect u) 0 = 0 := by
          simpa only [Matrix.cons_val_zero] using h0
        omega
    rcases hkOutside with hkLow | hkHigh
    · exact Or.inr (Or.inr (by
        rw [hvEq]
        exact (rlc_faithful_axisOutside_barrier_classify
          gamma gamma' hfaith hOutside).1 hkLow))
    · exact False.elim
        ((rlc_faithful_axisOutside_barrier_classify
          gamma gamma' hfaith hOutside).2 hkHigh)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨
      (gamma'.1.2.1 : Site 2) 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
  rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_contact
      hfaith q hN huNeg hreflected hkOutside with
    hbarrier | hleft | hright
  · exact Or.inl hbarrier
  · exact Or.inr (Or.inl hleft)
  · have hcarrier := rlc_reflected_axisCrossing_carrier_of_right_contact
      gamma gamma' hfaith huNeg hreflected hright
    have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
    have hfirstN := L.negativeAnchor_reachable hfaith hN
    exact Or.inr (Or.inr ⟨v,
      hfirstN.trans (q.reachable.trans huvGood.reachable), hright⟩)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_extremeAxis_reachableBarrier_contact_or_higherAxis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {N u v : Site 2} {k : Int}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk N u)
    (hN : rlc_dualReflect N =
      (![-1, L.boundary.height + 1] : Site 2))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkExtreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
      L.boundary.height + 1 < k) :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1 := by
  rcases hkExtreme with hkLow | hkHigh
  · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
        hfaith q hN huNeg huv hreflected (Or.inl hkLow) with
      hbarrier | hleft | hright
    · exact Or.inl hbarrier
    · exact Or.inr (Or.inl hleft)
    · exact Or.inr (Or.inr (Or.inl hright))
  · by_cases hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1
    · have hcarrier := rlc_reflected_axisCrossing_carrier_of_between
        gamma gamma' hfaith huv.1 hreflected (by
          have hlower := L.boundary.height_lower
          omega) hkUpper
      have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
      have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
        rw [Sym2.eq_iff] at hreflected
        rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
        · exact hv
        · have h0 := congrArg (fun z : Site 2 => z 0) hu
          have h0' : (rlc_dualReflect u) 0 = 0 := by
            simpa only [Matrix.cons_val_zero] using h0
          omega
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      exact Or.inr (Or.inr (Or.inr ⟨v,
        hfirstN.trans (q.reachable.trans huvGood.reachable),
        hvEq, hkHigh, hkUpper⟩))
    · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
          hfaith q hN huNeg huv hreflected (Or.inr (by omega)) with
        hbarrier | hleft | hright
      · exact Or.inl hbarrier
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))


theorem rlc_goodBoundary_walk_to_boxBoundary_meets_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (pGood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    ∃ z ∈ pGood.support,
      rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra hnone
  push Not at hnone
  have hpAvoid : ∀ z ∈ pGood.support,
      rlc_dualReflect z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    exact hnone z hz
  let hle : rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      hypercubicLattice 2 := fun _ _ h => h.1.1
  let pDual := (pGood.mapLe hle).map rlc_dualReflectLatticeHom
  let pAxis : (hypercubicLattice 2).Walk
      (![0, B.height + 1] : Site 2) (rlc_dualReflect u) :=
    pDual.copy hAzero rfl
  have hpAxisAvoid : ∀ z ∈ pAxis.support,
      z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    dsimp only [pAxis, pDual] at hz
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    exact hpAvoid z0 hz0
  have huNot : rlc_dualReflect u ∉
      rlc_connectorBarrier gamma gamma' :=
    hpAvoid u pGood.end_mem_support
  obtain ⟨pOut, hpOutAvoid⟩ :=
    rlc_connectorBoxBoundary_detour_avoidsBarrier
      gamma gamma' huBoundary huNot
  let p := pAxis.append pOut
  have hkLower : (gamma.1.1 : Site 2) 1 < B.height + 1 := by
    have hlower := B.height_lower
    omega
  have hkUpper : B.height + 1 ≤ (gamma'.1.2.1 : Site 2) 1 := by
    have hupper := B.height_upper
    omega
  obtain ⟨z, hz, hzBarrier⟩ :=
    rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper p
  dsimp only [p] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  exact hz.elim (fun hz => hpAxisAvoid z hz hzBarrier)
    (fun hz => hpOutAvoid z hz hzBarrier)


theorem rlc_goodBoundary_barrier_hit_before_boxBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    ∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  let k := B.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, k] : Site 2), ![0, k]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [k, Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hzeroMem : (![0, k] : Site 2) ∈
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) := by
    rw [htarget]
    exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hzeroMem
  obtain ⟨A, hfirstA, hAfirst, hAzero⟩ :
      ∃ A : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace A ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          A B.firstFace ∧
        rlc_dualReflect A = (![0, k] : Site 2) := by
    rcases hzeroMem with hfirst | hsecond
    · exact ⟨B.firstFace, Reachable.refl _, Reachable.refl _, hfirst.symm⟩
    · exact ⟨B.secondFace, hanchor.reachable,
        hanchor.reachable.symm, hsecond.symm⟩
  by_contra hnone
  push Not at hnone
  obtain ⟨pGood⟩ := hAfirst.trans hu
  have hpAvoid : ∀ z ∈ pGood.support,
      rlc_dualReflect z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz hbarrier
    apply hnone z (hfirstA.trans ⟨pGood.takeUntil z hz⟩)
    exact hbarrier
  let hle : rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤
      hypercubicLattice 2 := fun _ _ h => h.1.1
  let pDual := (pGood.mapLe hle).map rlc_dualReflectLatticeHom
  let pAxis : (hypercubicLattice 2).Walk
      (![0, k] : Site 2) (rlc_dualReflect u) := pDual.copy hAzero rfl
  have hpAxisAvoid : ∀ z ∈ pAxis.support,
      z ∉ rlc_connectorBarrier gamma gamma' := by
    intro z hz
    dsimp only [pAxis, pDual] at hz
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    exact hpAvoid z0 hz0
  have huNot : rlc_dualReflect u ∉
      rlc_connectorBarrier gamma gamma' := hnone u hu
  obtain ⟨pOut, hpOutAvoid⟩ :=
    rlc_connectorBoxBoundary_detour_avoidsBarrier
      gamma gamma' huBoundary huNot
  let p := pAxis.append pOut
  have hkLower : (gamma.1.1 : Site 2) 1 < k := by
    have hlower := B.height_lower
    dsimp only [k]
    omega
  have hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1 := by
    have hupper := B.height_upper
    dsimp only [k]
    omega
  obtain ⟨z, hz, hzBarrier⟩ :=
    rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier
      gamma gamma' hfaith hkLower hkUpper p
  dsimp only [p] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  exact hz.elim (fun hz => hpAxisAvoid z hz hzBarrier)
    (fun hz => hpOutAvoid z hz hzBarrier)


theorem rlc_goodBoundary_reachable_wall_or_region_incident
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj
            (rlc_dualReflect z) (rlc_dualReflect w) ∧
          rlc_dualReflect w ∈ rlc_connectorBox n ∧
          ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
            h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
  have hanchor := B.anchor_mem_goodBoundaryGraph hfaith
  have hincident : ∃ w : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj z w := by
    by_cases hzFirst : z = B.firstFace
    · subst z
      exact ⟨B.secondFace, hanchor⟩
    · obtain ⟨p⟩ := hz.symm
      cases p with
      | nil => exact False.elim (hzFirst rfl)
      | @cons a w c haw p => exact ⟨w, haw⟩
  obtain ⟨w, hzw⟩ := hincident
  rcases hzw.2 with hwall | ⟨hzBox, hwBox, hregion⟩
  · exact Or.inl (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _))
  · exact Or.inr ⟨w, (rlc_adj_dualReflect z w).mp hzw.1.1,
      hwBox, hregion⟩


theorem rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x z : Site 2}
    (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x z) :
    rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj
            (rlc_dualReflect z) (rlc_dualReflect w) ∧
          rlc_dualReflect w ∈ rlc_connectorBox n ∧
          ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
            h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
  by_cases hzx : z = x
  · subst z
    exact Or.inl hxBarrier
  · obtain ⟨p⟩ := hz.symm
    have hincident : ∃ w : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj z w := by
      cases p with
      | nil => exact False.elim (hzx rfl)
      | @cons a w c haw p => exact ⟨w, haw⟩
    obtain ⟨w, hzw⟩ := hincident
    rcases hzw.2 with hwall | ⟨_hzBox, hwBox, hregion⟩
    · exact Or.inl (rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hwall (Sym2.mem_mk_left _ _))
    · exact Or.inr ⟨w, (rlc_adj_dualReflect z w).mp hzw.1.1,
        hwBox, hregion⟩


theorem rlc_walk_subgraph_prefix_or_first_exit
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, ∀ e ∈ q.edges, e ∈ w.edges) ∨
      ∃ (u v : V) (q : G.Walk x u),
        H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧
          ∀ e ∈ q.edges, e ∈ w.edges := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, by simp⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, huv, huvW, huvBad, hq⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
        · right
          refine ⟨u, v, .cons habG q, huv, by simp [huvW], huvBad, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
      · right
        exact ⟨a, b, .nil, hab, by simp, habG, by simp⟩


theorem rlc_walk_subgraph_exact_or_first_exit
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, q.edges = w.edges) ∨
      ∃ (u v : V) (q : G.Walk x u),
        H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧
          ∀ e ∈ q.edges, e ∈ w.edges := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, huv, huvW, huvBad, hq⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          simp [SimpleGraph.Walk.edges_cons, hq]
        · right
          refine ⟨u, v, .cons habG q, huv, by simp [huvW], huvBad, ?_⟩
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
          exact he.elim Or.inl (fun he => Or.inr (hq e he))
      · right
        exact ⟨a, b, .nil, hab, by simp, habG, by simp⟩


theorem rlc_walk_subgraph_lift_or_first_exit_decomp
    {V : Type*} {G H : SimpleGraph V} (hle : G ≤ H)
    {x y : V} (w : H.Walk x y) :
    (∃ q : G.Walk x y, q.mapLe hle = w) ∨
      ∃ (u v : V) (q : G.Walk x u) (r : H.Walk v y)
        (huv : H.Adj u v),
        ¬ G.Adj u v ∧
          w = (q.mapLe hle).append (.cons huv r) := by
  induction w with
  | nil =>
      left
      exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
      by_cases habG : G.Adj a b
      · rcases ih with ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
        · left
          refine ⟨.cons habG q, ?_⟩
          simp only [SimpleGraph.Walk.map_cons]
          change q.map (.ofLE hle) = p at hq
          rw [hq]
          apply SimpleGraph.Walk.ext_support
          rfl
        · right
          refine ⟨u, v, .cons habG q, r, huv, huvBad, ?_⟩
          rw [hdecomp]
          apply SimpleGraph.Walk.ext_support
          simp [SimpleGraph.Walk.support_append,
            SimpleGraph.Walk.support_mapLe_eq_support]
      · right
        exact ⟨a, b, .nil, p, hab, habG, by simp⟩


theorem rlc_goodBoundary_prefix_or_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y,
      ∀ e ∈ q.edges, e ∈ w.edges) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u),
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ w.edges ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ∀ e ∈ q.edges, e ∈ w.edges := by
  rcases rlc_walk_subgraph_prefix_or_first_exit
      (G := rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho)
      w with hgood | hbad
  · exact Or.inl hgood
  · right
    obtain ⟨u, v, q, huv, huvW, huvBad, hq⟩ := hbad
    refine ⟨u, v, q, huv, huvW, ?_, hq⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩


theorem rlc_goodBoundary_exact_or_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y, q.edges = w.edges) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u),
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ w.edges ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ∀ e ∈ q.edges, e ∈ w.edges := by
  rcases rlc_walk_subgraph_exact_or_first_exit
      (G := rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho)
      w with hgood | ⟨u, v, q, huv, huvW, huvBad, hq⟩
  · exact Or.inl hgood
  · right
    refine ⟨u, v, q, huv, huvW, ?_, hq⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩


theorem rlc_goodBoundary_lift_or_first_bad_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x y : Site 2}
    (w : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y) :
    (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk x y,
      q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le
        gamma gamma' rho) = w) ∨
      ∃ (u v : Site 2)
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk x u)
        (r : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v y)
        (huv : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v),
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          w = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le
            gamma gamma' rho)).append (.cons huv r) := by
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle w with
      ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
  · exact Or.inl ⟨q, hq⟩
  · right
    refine ⟨u, v, q, r, huv, ?_, hdecomp⟩
    intro hcarrier
    exact huvBad ⟨huv, hcarrier⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  let last : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' u' :=
    hu'v'.symm.toWalk
  let m : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u u' :=
    .cons huv (t.reverse.append last)
  have huvA : s(u, v) ∈ a.edges := by
    rw [hdecomp, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_cons, List.mem_append]
    exact Or.inr (by simp)
  have hrA {e : Sym2 (Site 2)} (he : e ∈ r.edges) : e ∈ a.edges := by
    rw [hdecomp, SimpleGraph.Walk.edges_append, List.mem_append]
    exact Or.inr (by simp [he])
  have htR {e : Sym2 (Site 2)} (he : e ∈ t.edges) : e ∈ r.edges := by
    have heRev : e ∈ r.reverse.edges := by
      rw [hdecomp', SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_cons, List.mem_append]
      exact Or.inr (by simp [he])
    simpa [SimpleGraph.Walk.edges_reverse] using heRev
  have hu'v'R : s(u', v') ∈ r.edges := by
    have heRev : s(u', v') ∈ r.reverse.edges := by
      rw [hdecomp', SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_cons, List.mem_append]
      exact Or.inr (by simp)
    simpa [SimpleGraph.Walk.edges_reverse] using heRev
  have hmA : ∀ e ∈ m.edges, e ∈ a.edges := by
    intro e he
    simp only [m, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_append, List.mem_cons, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with rfl | he | he
    · exact huvA
    · exact hrA (htR he)
    · have heEq : e = s(v', u') := by
        simpa [last] using he
      subst e
      simpa [Sym2.eq_swap] using hrA hu'v'R
  obtain ⟨f, g, k, hfgM, hreflected, hextreme⟩ :=
    L.middlePath_axis_crossing_extreme m huNeg hu'Pos
      (by
        intro e he
        exact (haExact e).2 (Or.inr (hmA e he)))
      (by
        intro he
        exact haAvoid (hmA _ he))
  exact ⟨f, g, k, (haExact _).2 (Or.inr (hmA _ hfgM)),
    hreflected, hextreme⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_location_twoBadMiddle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    {f g : Site 2} (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
    (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(L.boundary.firstFace, L.boundary.secondFace) ∨
      s(f, g) ∈ q.edges ∨ s(f, g) ∈ q'.edges ∨ s(f, g) ∈ t.edges := by
  have bad_ne {x y : Site 2}
      (hxyBad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' x y)
      (heq : s(f, g) = s(x, y)) : False := by
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hfx, hgy⟩ | ⟨hfy, hgx⟩
    · subst f
      subst g
      exact hxyBad hfgGood
    · subst f
      subst g
      exact hxyBad
        ((rlc_reflectedEdgeCarrierGeometry_comm gamma gamma' y x).1 hfgGood)
  rcases (haExact s(f, g)).1 hfgContour with hanchor | hfa
  · exact Or.inl hanchor
  right
  rw [hdecomp, SimpleGraph.Walk.edges_append, List.mem_append] at hfa
  rcases hfa with hfq | hfr
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfq)
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hfr
  rcases hfr with hbadEdge | hfr
  · exact (bad_ne hbad hbadEdge).elim
  have hfrReverse : s(f, g) ∈ r.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hfr
  rw [hdecomp', SimpleGraph.Walk.edges_append, List.mem_append] at hfrReverse
  rcases hfrReverse with hfq' | hft
  · exact Or.inr (Or.inl (by
      simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfq'))
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hft
  rcases hft with hbadEdge' | hft
  · exact (bad_ne hbad' hbadEdge').elim
  · exact Or.inr (Or.inr hft)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_mem_middle_of_avoids_anchor_prefixes
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    {f g : Site 2} (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
    (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g)
    (havoidAnchor : s(f, g) ≠
      s(L.boundary.firstFace, L.boundary.secondFace))
    (havoidQ : s(f, g) ∉ q.edges) (havoidQ' : s(f, g) ∉ q'.edges) :
    s(f, g) ∈ t.edges := by
  rcases L.goodContourEdge_location_twoBadMiddle haExact q r huv hbad
      hdecomp q' t hu'v' hbad' hdecomp' hfgContour hfgGood with
    hanchor | hq | hq' | ht
  · exact (havoidAnchor hanchor).elim
  · exact (havoidQ hq).elim
  · exact (havoidQ' hq').elim
  · exact ht


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementaryPath_good_or_two_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      a.IsPath ∧
      (∀ e : Sym2 (Site 2),
        e ∈ L.boundary.contour.edges ↔
          e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
            e ∈ a.edges) ∧
      ((∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk L.boundary.firstFace L.boundary.secondFace,
          q.edges = a.edges) ∨
        ∃ (u v u' v' : Site 2)
          (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
            L.boundary.firstFace u)
          (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
            L.boundary.secondFace u'),
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
          s(u, v) ∈ a.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v' ∧
          s(u', v') ∈ a.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') := by
  obtain ⟨a, haPath, _haAvoid, haExact⟩ :=
    L.complementary_axis_path_exact
  refine ⟨a, haPath, haExact, ?_⟩
  rcases rlc_goodBoundary_exact_or_first_bad a with
      ⟨q, hqEdges⟩ | ⟨u, v, q, huv, huvA, hbad, _hqA⟩
  · exact Or.inl ⟨q, hqEdges⟩
  · rcases rlc_goodBoundary_exact_or_first_bad a.reverse with
        ⟨q', hq'Edges⟩ | ⟨u', v', q', hu'v', hu'v'A, hbad', _hq'A⟩
    · exfalso
      have huvRev : s(u, v) ∈ a.reverse.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using huvA
      have huvQ : s(u, v) ∈ q'.edges := by
        rw [hq'Edges]
        exact huvRev
      exact hbad (q'.adj_of_mem_edges huvQ).2
    · exact Or.inr ⟨u, v, u', v', q, q', huv, huvA, hbad, hu'v',
        by simpa [SimpleGraph.Walk.edges_reverse] using hu'v'A, hbad'⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.reachableFaithfulContacts_of_complementaryPath_good
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace L.boundary.secondFace)
    (hqEdges : q.edges = a.edges) :
    ∃ x y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x y ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
  have hanchorGood := L.boundary.anchor_mem_goodBoundaryGraph hfaith
  have reachable_of_contour {z : Site 2}
      (hz : z ∈ L.boundary.contour.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace z := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with hz | ⟨e, he, hze⟩
    · subst z
      exact Reachable.refl _
    · rcases (haExact e).1 he with heAnchor | heA
      · subst e
        rw [Sym2.mem_iff] at hze
        rcases hze with rfl | rfl
        · exact Reachable.refl _
        · exact hanchorGood.reachable
      · have heQ : e ∈ q.edges := by
          rw [hqEdges]
          exact heA
        have hzQ : z ∈ q.support := by
          rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
          exact Or.inr ⟨e, heQ, hze⟩
        exact ⟨q.takeUntil z hzQ⟩
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupport
  obtain ⟨y', hyy'⟩ := hySupport
  have hxe : s(x, x') ∈ L.boundary.contour.edges :=
    L.boundary.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hxx')
  have hye : s(y, y') ∈ L.boundary.contour.edges :=
    L.boundary.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hyy')
  have hxContour := L.boundary.contour.fst_mem_support_of_mem_edges hxe
  have hyContour := L.boundary.contour.fst_mem_support_of_mem_edges hye
  exact ⟨x, y, (reachable_of_contour hxContour).symm.trans
    (reachable_of_contour hyContour), hxPath, hyPath⟩


theorem rlc_goodBoundary_first_barrier_incoming_region_flank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {A z : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A z)
    (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
    (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
    ∃ (u v : Site 2)
      (q : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Walk A u),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj u v ∧
        s(u, v) ∈ p.edges ∧
        (∀ e ∈ q.edges, e ∈ p.edges) ∧
        (∀ w ∈ q.support,
          rlc_dualReflect w ∉ rlc_connectorBarrier gamma gamma') ∧
        rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  let P : Site 2 → Prop := fun w =>
    rlc_dualReflect w ∉ rlc_connectorBarrier gamma gamma'
  obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqAvoid, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p P hA (by
      simpa only [P, not_not] using hz)
  have hvBarrier : rlc_dualReflect v ∈
      rlc_connectorBarrier gamma gamma' := by
    simpa only [P, not_not] using hv
  have hnotWall : s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    intro hwall
    have huBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _)
    exact (hqAvoid u q.end_mem_support) huBarrier
  rcases huv.2 with hwall | hregion
  · have huBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' hwall (Sym2.mem_mk_left _ _)
    exact False.elim ((hqAvoid u q.end_mem_support) huBarrier)
  · exact ⟨u, v, q, huv, huvEdge, hqEdges, hqAvoid, hvBarrier, hnotWall,
      hregion.1, hregion.2.1, hregion.2.2⟩


theorem rlc_goodBoundary_first_barrier_contact_boundary_or_extend
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {A z : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A z)
    (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
    (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
    ∃ (u v b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable A v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧
      u ≠ b ∧
      rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧
      (rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
        rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
        ¬ (-2 * n < (rlc_dualReflect v) 0 ∧
          (rlc_dualReflect v) 0 < 2 * n ∧
          -n < (rlc_dualReflect v) 1 ∧
          (rlc_dualReflect v) 1 < n) ∨
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj v b) := by
  obtain ⟨u, v, q, huv, _huvEdge, _hqEdges, _hqAvoid,
      hvBarrier, hnotIn, _huBox, _hvBox, h, hhRegion, hh⟩ :=
    rlc_goodBoundary_first_barrier_incoming_region_flank p hA hz
  obtain ⟨b, hvb, hub⟩ :=
    rlc_connectorCentralFaceFilledBoundary_other_neighbor
      gamma gamma' rho huv.1
  refine ⟨u, v, b, q.reachable.trans huv.reachable, hvb, hub,
    hvBarrier, ?_⟩
  by_cases hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n
  · rcases lt_trichotomy (rlc_dualReflect v 0) 0 with hvNeg | hvZero | hvPos
    · rcases rlc_negativeBarrier_continuation_or_left_contact
        gamma gamma' rho hno huv.1 hvb hub hvNeg hvBarrier hvInterior
          (by simpa [Sym2.eq_swap] using hnotIn) hhRegion
          (by simpa [flankFaces_comm] using hh) with
          hvLeft | hcarrier
      · exact Or.inr (Or.inl hvLeft)
      · exact Or.inr (Or.inr (Or.inr ⟨hvb, hcarrier⟩))
    · have hvEq : rlc_dualReflect v =
          (![0, (rlc_dualReflect v) 1] : Site 2) := by
        ext i
        fin_cases i
        · simpa using hvZero
        · rfl
      have hvBarrier' : (![0, (rlc_dualReflect v) 1] : Site 2) ∈
          rlc_connectorBarrier gamma gamma' := by
        rwa [← hvEq]
      have hvAxis := (rlc_axis_mem_connectorBarrier_iff gamma gamma'
        ((rlc_dualReflect v) 1)).1 hvBarrier'
      rcases hvAxis with hvRight | hvLeft
      · exact Or.inl (by rwa [hvEq])
      · exact Or.inr (Or.inl (by rwa [hvEq]))
    · rcases rlc_positiveBarrier_continuation_or_right_contact
        gamma gamma' rho hno huv.1 hvb hub hvPos hvBarrier hvInterior
          (by simpa [Sym2.eq_swap] using hnotIn) hhRegion
          (by simpa [flankFaces_comm] using hh) with
          hvRight | hcarrier
      · exact Or.inl hvRight
      · exact Or.inr (Or.inr (Or.inr ⟨hvb, hcarrier⟩))
  · exact Or.inr (Or.inr (Or.inl hvInterior))


theorem rlc_goodBoundary_first_bad_toward
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {z : Site 2}
    (hz : z ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    ∃ u v : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace u ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
        ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace v := by
  have hfirst : B.firstFace ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support :=
    B.anchor_adj.mem_support_left
  obtain ⟨w⟩ := rlc_connectorCentralFaceFilledFaceBoundary_reachable
    gamma gamma' rho hfirst hz
  obtain ⟨u, v, huvEdge, hu, hv⟩ := rlc_walk_pred_first_exit w
    (fun a => (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace a)
    (Reachable.refl _) hzNot
  have huv := w.adj_of_mem_edges huvEdge
  refine ⟨u, v, hu, huv, ?_, hv⟩
  intro hcarrier
  have hgood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
  exact hv (hu.trans hgood.reachable)


theorem rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x u v : Site 2}
    (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
    (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra huBarrier
  rcases rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start
      hxBarrier hu with huWall | ⟨w, huw, _hwBox, h, hhRegion, hhFlank⟩
  · exact huBarrier huWall
  · have huvTarget := (rlc_adj_dualReflect u v).mp huv.1
    have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box_of_start
      hxBox hu
    have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
      omega
    generalize hkEq : flankFaces (rlc_dualReflect u) (rlc_dualReflect v) = e
    induction e using Sym2.inductionOn with
    | _ k l =>
        have hkFlank : k ∈
            flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
          rw [hkEq]
          exact Sym2.mem_mk_left _ _
        have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
          gamma gamma' huw huvTarget huInterior huBarrier
            hhRegion hhFlank hkFlank
        apply hbad
        exact Or.inr ⟨huBox, hvBox, k, hkRegion, hkFlank⟩


theorem rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  by_contra huBarrier
  rcases rlc_goodBoundary_reachable_wall_or_region_incident
      B hfaith hu with huWall | ⟨w, huw, _hwBox, h, hhRegion, hhFlank⟩
  · exact huBarrier huWall
  · have huvTarget := (rlc_adj_dualReflect u v).mp huv.1
    have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      B hfaith hu
    have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
      omega
    generalize hkEq : flankFaces (rlc_dualReflect u) (rlc_dualReflect v) = e
    induction e using Sym2.inductionOn with
    | _ k l =>
        have hkFlank : k ∈
            flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
          rw [hkEq]
          exact Sym2.mem_mk_left _ _
        have hkRegion := rlc_centralFaceRegion_flank_transfer_interior
          gamma gamma' huw huvTarget huInterior huBarrier
            hhRegion hhFlank hkFlank
        apply hbad
        exact Or.inr ⟨huBox, hvBox, k, hkRegion, hkFlank⟩


theorem rlc_badExit_interior_nonwall_box_noCentralFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {u v : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    s(rlc_dualReflect u, rlc_dualReflect v) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      rlc_dualReflect u ∈ rlc_connectorBox n ∧
      rlc_dualReflect v ∈ rlc_connectorBox n ∧
      ∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have huvTarget : (hypercubicLattice 2).Adj
      (rlc_dualReflect u) (rlc_dualReflect v) :=
    (rlc_adj_dualReflect u v).mp huv.1
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    omega
  have hvBox : rlc_dualReflect v ∈ rlc_connectorBox n := by
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at huvTarget
    omega
  have hnotWall : s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    intro hwall
    exact hbad (Or.inl hwall)
  refine ⟨hnotWall, huBox, hvBox, ?_⟩
  intro h hhRegion hhFlank
  exact hbad (Or.inr ⟨huBox, hvBox, h, hhRegion, hhFlank⟩)


theorem rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
      (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · exact Or.inl
      (rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        B hfaith hu huv hbad huInterior)
  · push Not at huInterior
    omega


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      ∃ w ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect u = rlc_flipX w ∧
          ∀ a : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Adj a u →
            a ≠ v →
            s(rlc_dualReflect a, rlc_dualReflect u) ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    L.boundary hfaith hu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr (Or.inl huBoundary)
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        L.boundary hfaith hu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · have huRect := rlc_pathVertex_mem_rect gamma.1 huRight
      rw [mem_rect] at huRect
      omega
    · exact Or.inl ⟨u, hu, huLeft⟩
    · omega
    · obtain ⟨_huNeg, w, hw, huw⟩ := huFlipRight
      by_cases hwall : ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr (Or.inr ⟨w, hw, huw, hwall⟩)
      · simp only [not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huLeft := rlc_negativeBarrier_bad_exit_forces_left_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall huNeg
            huBarrier huInterior hbad
        exact Or.inl ⟨u, hu, huLeft⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w ∧
          ∀ a : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Adj a u →
            a ≠ v →
            s(rlc_dualReflect a, rlc_dualReflect u) ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    L.boundary hfaith hu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr (Or.inl huBoundary)
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        L.boundary hfaith hu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, hu, huRight⟩
    · have huRect := rlc_pathVertex_mem_rect gamma'.1 huLeft
      rw [mem_rect] at huRect
      omega
    · obtain ⟨_huPos, w, hw, huw⟩ := huFlipLeft
      by_cases hwall : ∀ a : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj a u →
          a ≠ v →
          s(rlc_dualReflect a, rlc_dualReflect u) ∈
            rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inr (Or.inr ⟨w, hw, huw, hwall⟩)
      · simp only [not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huRight := rlc_positiveBarrier_bad_exit_forces_right_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall huPos
            huBarrier huInterior hbad
        exact Or.inl ⟨u, hu, huRight⟩
    · omega


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno hu huNeg huv hbad with hleft | hboundary | hwall
  · exact Or.inl hleft
  · exact Or.inr (rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu hboundary)
  · obtain ⟨w, hw, huw, _hwall⟩ := hwall
    refine Or.inr ⟨u, hu, ?_⟩
    simp [rlc_connectorBarrier, huw, hw]


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_barrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
      hfaith hno hu huPos huv hbad with hright | hboundary | hwall
  · exact Or.inl hright
  · exact Or.inr (rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu hboundary)
  · obtain ⟨w, hw, huw, _hwall⟩ := hwall
    refine Or.inr ⟨u, hu, ?_⟩
    simp [rlc_connectorBarrier, huw, hw]


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachable_or_negativeBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ (x : Site 2) (k : Int),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1) ∨
      ∃ u v : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace u ∧
          (rlc_dualReflect u) 0 < 0 ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
              u v ∧
          s(u, v) ∈ L.boundary.contour.edges ∧
          ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
          (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
            (rlc_dualReflect u) 0 = -2 * n ∨
            (rlc_dualReflect u) 0 = 2 * n ∨
            (rlc_dualReflect u) 1 = -n ∨
            (rlc_dualReflect u) 1 = n) := by
  obtain ⟨a, N, u, v, k, q, _hNside, hN, _haAvoid, _haPath, _haExact,
      haEdges, hqA, hqNeg, huv, _huvA, hreflected, hkLow | hkHigh⟩ :=
    L.complementary_first_axis_crossing_extreme
  · rcases rlc_goodBoundary_prefix_or_first_bad q with
      ⟨qGood, _hqGood⟩ |
        ⟨ub, vb, qGood, hubv, hubvQ, hbad, _hqGood⟩
    · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
          hfaith qGood hN (hqNeg u q.end_mem_support) huv hreflected
            (Or.inl hkLow) with hbarrier | hleft | hright
      · exact Or.inl hbarrier
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))
    · have hubNeg := hqNeg ub (q.fst_mem_support_of_mem_edges hubvQ)
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      have hubReach := hfirstN.trans qGood.reachable
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ub, vb, hubReach,
        hubNeg, hubv, haEdges _ (hqA _ hubvQ), hbad,
        rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          L.boundary hfaith hubReach hubv hbad⟩)))
  · rcases rlc_goodBoundary_prefix_or_first_bad q with
      ⟨qGood, _hqGood⟩ |
        ⟨ub, vb, qGood, hubv, hubvQ, hbad, _hqGood⟩
    · have huNeg := hqNeg u q.end_mem_support
      by_cases hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1
      · have hcarrier := rlc_reflected_axisCrossing_carrier_of_between
          gamma gamma' hfaith huv.1 hreflected (by
            have hlower := L.boundary.height_lower
            omega) hkUpper
        have huvGood : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Adj u v := ⟨huv, hcarrier⟩
        have hvEq : rlc_dualReflect v = (![0, k] : Site 2) := by
          rw [Sym2.eq_iff] at hreflected
          rcases hreflected with ⟨_hu, hv⟩ | ⟨hu, _hv⟩
          · exact hv
          · have h0 := congrArg (fun z : Site 2 => z 0) hu
            have h0' : (rlc_dualReflect u) 0 = 0 := by
              simpa only [Matrix.cons_val_zero] using h0
            omega
        have hfirstN := L.negativeAnchor_reachable hfaith hN
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, k,
          hfirstN.trans (qGood.reachable.trans huvGood.reachable),
          hvEq, hkHigh, hkUpper⟩)))
      · rcases L.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact
            hfaith qGood hN huNeg huv hreflected (Or.inr (by omega)) with
          hbarrier | hleft | hright
        · exact Or.inl hbarrier
        · exact Or.inr (Or.inl hleft)
        · exact Or.inr (Or.inr (Or.inl hright))
    · have hubNeg := hqNeg ub (q.fst_mem_support_of_mem_edges hubvQ)
      have hfirstN := L.negativeAnchor_reachable hfaith hN
      have hubReach := hfirstN.trans qGood.reachable
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ub, vb, hubReach,
        hubNeg, hubv, haEdges _ (hqA _ hubvQ), hbad,
        rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          L.boundary hfaith hubReach hubv hbad⟩)))


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachableBarrier_contact_or_higherAxis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    (∃ z : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace z ∧
        rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (x : Site 2) (k : Int),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          rlc_dualReflect x = (![0, k] : Site 2) ∧
          L.boundary.height + 1 < k ∧
          k ≤ (gamma'.1.2.1 : Site 2) 1 := by
  rcases L.complementary_first_axis_crossing_reachable_or_negativeBad
      hfaith with hbarrier | hleft | hright | hhigher |
        ⟨u, v, hu, huNeg, huv, _huvContour, hbad, _huClass⟩
  · exact Or.inl hbarrier
  · exact Or.inr (Or.inl hleft)
  · exact Or.inr (Or.inr (Or.inl hright))
  · exact Or.inr (Or.inr (Or.inr hhigher))
  · rcases L.negativeBadExit_reachable_left_or_barrier
        hfaith hno hu huNeg huv hbad with hleft | hbarrier
    · exact Or.inr (Or.inl hleft)
    · exact Or.inl hbarrier


theorem rlc_goodBoundary_walk_barrier_before_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u v : Site 2}
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A B.firstFace)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk B.firstFace u)
    (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    ∃ z ∈ (pA.append q).support,
      rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  have hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace u := q.reachable
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · refine ⟨u, ?_, rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
      B hfaith hu huv hbad huInterior⟩
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr q.end_mem_support
  · have huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n := by
      push Not at huInterior
      omega
    exact rlc_goodBoundary_walk_to_boxBoundary_meets_barrier
      B hfaith (pA.append q) hAzero huBoundary


theorem rlc_goodBoundary_barrier_hit_before_first_bad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
    (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace z) :
    ∃ u : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          B.firstFace u ∧
        rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
  obtain ⟨u, v, hu, huv, hbad, _hv⟩ :=
    rlc_goodBoundary_first_bad_toward B hz hzNot
  have huBox := rlc_goodBoundary_reachable_dualReflect_mem_box
    B hfaith hu
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
  rw [mem_rect] at huBox
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · exact ⟨u, hu,
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior
        B hfaith hu huv hbad huInterior⟩
  · have huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n := by
      push Not at huInterior
      omega
    exact rlc_goodBoundary_barrier_hit_before_boxBoundary
      B hfaith hu huBoundary


end
end StatMech.Universality
