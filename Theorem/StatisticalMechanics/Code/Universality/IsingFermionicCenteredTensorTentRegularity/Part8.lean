/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part7


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds
    (L : NNReal) (N : Nat)
    (hI : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b,
      isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q →
        FKIsingExpandingCenteredHorizontalNeighborBound L k a b)
    (hJ : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b,
      isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q →
        FKIsingExpandingCenteredVerticalNeighborBound L k a b) :
    FKIsingExpandingCenteredNeighborTransport := by
  refine ⟨L, N, ?_⟩
  intro k hk
  constructor
  · intro a b ha hb
    exact hI (isingCenteredRadialIndexSector
      (fkIsingExpandingSquareSide k) a b) k hk a b rfl ha hb
  · intro a b ha hb
    exact hJ (isingCenteredRadialIndexSector
      (fkIsingExpandingSquareSide k) a b) k hk a b rfl ha hb


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredNeighbor
    (hneighbor : FKIsingExpandingCenteredNeighborTransport) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
  obtain ⟨L, N, hN⟩ := hneighbor
  constructor
  intro K hK _hKU
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Complex)).mp hK.isBounded
  let R0 : Real := max R 0
  have hR0 : 0 <= R0 := le_max_right _ _
  have hKR0 : K ⊆ closedBall (0 : Complex) R0 :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hevent :=
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (2 * R0) 4
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Nr, hNr⟩ := hevent
  let M : Nat := max N Nr
  obtain ⟨Cpre, hpre⟩ :=
    exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
      K hK M
  refine ⟨max Cpre (4 * L), 1, by norm_num, ?_⟩
  intro k
  apply LipschitzOnWith.holderOnWith
  by_cases hk : k < M
  · exact (hpre k hk).weaken (le_max_left _ _)
  · have hMk : M <= k := by omega
    have hNk : N <= k := le_trans (le_max_left N Nr) hMk
    have hNrk : Nr <= k := le_trans (le_max_right N Nr) hMk
    have hrad := hNr k hNrk
    have hwide : 2 * R0 + 4 * fkIsingExpandingSquareScale k <=
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k := by
      nlinarith
    have hbound := hN k hNk
    exact
      ((fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor
          k R0 L hR0 hwide hbound.1 hbound.2).mono hKR0).weaken
        (le_max_right _ _)


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor
    (hneighbor : FKIsingExpandingCenteredStrictNeighborTransport) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
  obtain ⟨L, N, hN⟩ := hneighbor
  constructor
  intro K hK _hKU
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Complex)).mp hK.isBounded
  let R0 : Real := max R 0
  have hR0 : 0 <= R0 := le_max_right _ _
  have hKR0 : K ⊆ closedBall (0 : Complex) R0 :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hevent :=
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (2 * R0) 5
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Nr, hNr⟩ := hevent
  let M : Nat := max N Nr
  obtain ⟨Cpre, hpre⟩ :=
    exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
      K hK M
  refine ⟨max Cpre (4 * L), 1, by norm_num, ?_⟩
  intro k
  apply LipschitzOnWith.holderOnWith
  by_cases hk : k < M
  · exact (hpre k hk).weaken (le_max_left _ _)
  · have hMk : M <= k := by omega
    have hNk : N <= k := le_trans (le_max_left N Nr) hMk
    have hNrk : Nr <= k := le_trans (le_max_right N Nr) hMk
    have hrad := hNr k hNrk
    have hwide : 2 * R0 + 5 * fkIsingExpandingSquareScale k <=
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k := by
      nlinarith
    have hbound := hN k hNk
    exact
      ((fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor
          k R0 L hR0 hwide hbound.1 hbound.2).mono hKR0).weaken
        (le_max_right _ _)


theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch
    (n m a b : Nat) (hn : 0 < n) (hm : m ≤ n)
    (ha : a < m) (hb : b < m) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    fkIsingSquareBoundaryRadialPatchFullObservable]
  rw [fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge
    n m a b hm ha hb]


theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
        ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩ =
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
        n m baseI baseJ R hn hm hfitI hfitJ p := by
  unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch


theorem
    fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
            ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨n + (baseI + p'.1.1), by have := p'.1.2; omega⟩
            ⟨n + (baseJ + p'.2.1), by have := p'.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * H := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
      n m baseI baseJ R hn hm hfitI hfitJ p,
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
      n m baseI baseJ R hn hm hfitI hfitJ p']
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho mesh d H V hn hm hm2
      hfitI hfitJ hmesh r hdeep hV hd hH hradius hscale
      p p' hrho hp hp' hpp'


theorem
    fkIsingSquareBoundaryCenteredRadialPatch_add_side_cell_edges_halfScale
    (n m baseI baseJ R rho cutoff : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hcutoff : 0 < cutoff)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
    (hmcutoff : m ≤ 2 * cutoff) (hmrho : m ≤ 2 * rho)
    (a b : Nat) (ha0 : 0 < a) (haR : a < R)
    (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
    let F : IsingLeapfrogBox R → Complex := fun p ↦
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
        ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩
    let normalization := Real.sqrt (2 * (1 / (m : Real)))
    let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
    ‖F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤
          2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta := by
  let F : IsingLeapfrogBox R → Complex := fun p ↦
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
      ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩
  have hF : F = fkIsingSquareBoundaryRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ := by
    funext p
    exact
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
        n m baseI baseJ R hn hm hfitI hfitJ p
  have h :=
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale
      n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
      hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho
      hmarginN hmarginE hmarginS hmarginW
  rw [← hF] at h
  simpa only [F] using h


theorem
    fkIsingSquareBoundaryCenteredRadialPatch_normalizedNeighbor_norm_sub_le_of_radialWindow
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m <= n) (hm2 : 2 <= m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : forall q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r <= V)
    (hd : 0 <= d) (hH : 0 <= H)
    (hradius : d <= mesh * (rho : Real))
    (hscale : 1032080 * V <= H ^ 2 * d ^ 3)
    (i j i' j' : Fin (2 * n))
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p')
    (hfirst :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j =
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p)
    (hsecond :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' =
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p') :
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' /
          (Real.sqrt (2 * mesh) : Complex)) <= mesh * H := by
  rw [hfirst, hsecond]
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh
      r hdeep hV hd hH hradius hscale p p' hrho hp hp' hpp'

end
end StatMech.Universality
