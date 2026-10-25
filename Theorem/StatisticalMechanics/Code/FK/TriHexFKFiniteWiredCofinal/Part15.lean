/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part14
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict
    (n : Nat) :
    triHexPlanarTriBufferedRootBoundaryEvent (n + 1) ⊆
      ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹'
        triHexPlanarFiniteTriangleRootBoundaryEvent n := by
  simpa only [triHexPlanarTriBufferedRootBoundaryEvent,
    triHexPlanarFiniteTriangleRootBoundaryEvent,
    triHexPlanarFiniteTriangleToBuffered_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triHexPlanarFiniteTriangleInducedGraph n)
      (triangular.bufferedGraph (n + 2))
      (triHexPlanarFiniteTriangleToBuffered n)
      (triHexPlanarFiniteBoundary n)
      (triangular.bufferedBoundary (n + 2))
      (triHexPlanarFiniteTriangleToBuffered_adjMatch n)
      (triHexPlanarFiniteTriangleToBuffered_not_boundary n)
      (triHexPlanarFiniteTriangleToBuffered_cross_boundary n)
      (triHexPlanarFiniteTriangleRoot n)

theorem triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict
    (n : Nat) :
    triHexPlanarFiniteTriangleRootBoundaryEvent
        (triHexPlanarTriBufferedOuterLevel (n + 1)) ⊆
      ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal (n + 1)) ⁻¹'
        triHexPlanarTriBufferedRootBoundaryEvent n := by
  simpa only [triHexPlanarTriBufferedRootBoundaryEvent,
    triHexPlanarFiniteTriangleRootBoundaryEvent,
    triHexPlanarTriBufferedToFiniteTerminal_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triangular.bufferedGraph (n + 1))
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel (n + 1)))
      (triHexPlanarTriBufferedToFiniteTerminal (n + 1))
      (triangular.bufferedBoundary (n + 1))
      (triHexPlanarFiniteBoundary
        (triHexPlanarTriBufferedOuterLevel (n + 1)))
      (triHexPlanarTriBufferedToFiniteTerminal_adjMatch (n + 1))
      (triHexPlanarTriBufferedToFiniteTerminal_not_boundary (n + 1))
      (triHexPlanarTriBufferedToFiniteTerminal_cross_boundary (n + 1))
      (triHexPlanarTriBufferedRoot n)

theorem triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass
    (n : Nat) {p q : Real} :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q =
      finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent n) := by
  classical
  unfold triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
    finiteWiredEventMass
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold triHexPlanarFiniteTriangleInducedBoundaryReachIndicator
    triHexPlanarFiniteTriangleRootBoundaryEvent finiteRootBoundaryEvent
    triHexPlanarFiniteTriangleRoot
  have hgraph := openSub_extendActive_restrictActive_eq
    (triHexPlanarFiniteTriangleInducedGraph n) omega
  have hiff : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n)
        (extendActive (triHexPlanarFiniteTriangleInducedGraph n)
          (restrictActive (triHexPlanarFiniteTriangleInducedGraph n) omega))).Reachable
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) y) ↔
    ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n) omega).Reachable
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) y := by
    simpa only [hgraph]
  rw [if_congr hiff rfl rfl]
  simp only [Set.indicator]
  rfl


theorem triHexPlanarTriBuffered_mass_le_triangle
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent (n + 1)) ≤
      triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent (n + 1)) ≤
      finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹'
          triHexPlanarFiniteTriangleRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict n)
    _ ≤ finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent n) :=
      triHexPlanarFiniteTriangle_outerBuffered_dominated n hp hp1 hq
        (finiteRootBoundaryEvent_isIncreasing _ _ _)


theorem triHexPlanarFiniteTriangle_le_triBuffered_mass
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
        (triHexPlanarTriBufferedOuterLevel (n + 1)) p q ≤
      finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel (n + 1)))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel (n + 1))) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent
          (triHexPlanarTriBufferedOuterLevel (n + 1))) ≤
      finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel (n + 1)))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel (n + 1))) p q
        (ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal (n + 1)) ⁻¹'
          triHexPlanarTriBufferedRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict n)
    _ ≤ finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) :=
      triHexPlanarTriBuffered_outerTriangle_dominated (n + 1)
        hp hp1 hq (finiteRootBoundaryEvent_isIncreasing _ _ _)

theorem triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary
    (n : Nat) :
    triHexPlanarTriBufferedRootBoundaryEvent n =
      triangular.bufferedSetBoundaryEvent
        ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1) := by
  ext eta
  constructor
  · rintro ⟨y, hy, hreach⟩
    exact ⟨triHexPlanarTriBufferedRoot n, Set.mem_singleton _,
      y, hy, hreach⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    have hx' : x = triHexPlanarTriBufferedRoot n := by
      apply Subtype.ext
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact ⟨y, hy, hreach⟩

theorem triHexPlanarTriBuffered_eventMass_eq_measure
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) =
      (triangular.wiredBufferedMeasure (n + 1) hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (n + 1)
          (triangular.bufferedSetBoundaryEvent
            ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1))) := by
  rw [triangular.wiredBufferedMeasure_real_cylinder (le_refl (n + 1))
    hp hp1 hq]
  unfold finiteWiredEventMass
  rw [triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary]
  apply Finset.sum_congr rfl
  intro omega _
  rfl

theorem triHexPlanarTriBuffered_eventMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => finiteWiredEventMass
        (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n)) atTop
      (nhds ((triangular.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 (Site 2)))).real
          (triangular.setHitsInfinite
            ({triHexPlanarTriRoot} : Set (Site 2))))) := by
  have hdiag := triangular.wiredBufferedSetBoundary_diag_tendsto
    ({triHexPlanarTriRoot} : Set (Site 2)) (Set.finite_singleton _)
    1 (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (triHexPlanarTriBufferedRoot 0).2)
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with n
  rw [triHexPlanarTriBuffered_eventMass_eq_measure n hp hp1
    (zero_lt_one.trans_le hq)]
  rw [Nat.one_add]

theorem triHexPlanarTriCofinalLevel_tendsto :
    Tendsto (fun n => triHexPlanarTriBufferedOuterLevel (n + 1))
      atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  unfold triHexPlanarTriBufferedOuterLevel
  exact Nat.add_lt_add_right
    (triangular.bufferedRadius_strictMono
      (Nat.add_lt_add_right (Nat.add_lt_add_right hab 1) 1)) 1


theorem triHexPlanar_fixedRootInfinite_real_eq
    {p q : Real} (hq : 1 ≤ q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    (hexagonal.wiredBufferedInfiniteVolume
        (BeffaraDC.dualParam_pos hp.1 hp.2 (zero_lt_one.trans_le hq))
        (BeffaraDC.dualParam_lt_one hp.1 hp.2 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.setHitsInfinite
        ({triHexPlanarHexWhiteRoot} : Set HexVertex)) =
    (triangular.wiredBufferedInfiniteVolume hp.1 hp.2
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.setHitsInfinite
        ({triHexPlanarTriRoot} : Set (Site 2))) := by
  let pd := BeffaraDC.dualParam p q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpd0 : 0 < pd := BeffaraDC.dualParam_pos hp.1 hp.2 hq0
  have hpd1 : pd < 1 := BeffaraDC.dualParam_lt_one hp.1 hp.2 hq0
  let cHex := fun n => finiteWiredEventMass
    (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1)) pd q
    (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)
  let cTri := fun n => finiteWiredEventMass
    (triangular.bufferedGraph (n + 1))
    (triangular.bufferedBoundary (n + 1)) p q
    (triHexPlanarTriBufferedRootBoundaryEvent n)
  have hcHex := triHexPlanarHexWhiteBuffered_eventMass_tendsto
    hpd0 hpd1 hq
  have hcTri := triHexPlanarTriBuffered_eventMass_tendsto
    hp.1 hp.2 hq
  apply le_antisymm
  · have hindex : Tendsto
        (fun n => triHexPlanarTriBufferedOuterLevel (n + 1) + 1)
        atTop atTop :=
      (tendsto_add_atTop_nat 1).comp triHexPlanarTriCofinalLevel_tendsto
    have hlo : Tendsto
        (fun n => cHex
          (triHexPlanarTriBufferedOuterLevel (n + 1) + 1)) atTop _ :=
      hcHex.comp hindex
    apply le_of_tendsto_of_tendsto hlo hcTri
    filter_upwards with n
    have heq :=
      triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
        (triangular.bufferedRadius (n + 2)) hq0 hp hsurface
    calc
      cHex (triHexPlanarTriBufferedOuterLevel (n + 1) + 1) ≤
          triHexPlanarFiniteStarWiredBoundaryProbability
            (triHexPlanarTriBufferedOuterLevel (n + 1)) pd q := by
        exact triHexPlanarHexWhiteBuffered_mass_le_star
          (triHexPlanarTriBufferedOuterLevel (n + 1)) hpd0 hpd1 hq
      _ = triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
            (triHexPlanarTriBufferedOuterLevel (n + 1)) p q := by
        simpa [pd, triHexPlanarTriBufferedOuterLevel, Nat.add_assoc] using heq
      _ ≤ cTri n := by
        exact triHexPlanarFiniteTriangle_le_triBuffered_mass
          n hp.1 hp.2 hq
  · have hindex : Tendsto
        (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)
        atTop atTop :=
      (tendsto_add_atTop_nat 1).comp
        triHexPlanarHexStarCofinalLevel_tendsto
    have hlo : Tendsto
        (fun n => cTri
          (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)) atTop _ :=
      hcTri.comp hindex
    apply le_of_tendsto_of_tendsto hlo hcHex
    filter_upwards with n
    have heq :=
      triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
        (hexagonal.bufferedRadius (n + 2)) hq0 hp hsurface
    calc
      cTri (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1) ≤
          triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
            (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q := by
        exact triHexPlanarTriBuffered_mass_le_triangle
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)) hp.1 hp.2 hq
      _ = triHexPlanarFiniteStarWiredBoundaryProbability
            (triHexPlanarHexBufferedOuterStarLevel (n + 1)) pd q := by
        simpa [pd, triHexPlanarHexBufferedOuterStarLevel,
          Nat.add_assoc] using heq.symm
      _ ≤ cHex n := by
        exact triHexPlanarFiniteStar_le_hexWhiteBuffered_mass
          n hpd0 hpd1 hq

end
end StatMech.FK.PeriodicPlanar
