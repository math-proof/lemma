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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part9
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteStarToHexBuffered_cross_boundary
    (n : Nat) (x : TriHexPlanarFiniteStarVertex n)
    (c : hexagonal.BufferedVertex (n + 2))
    (hadj : (hexagonal.bufferedGraph (n + 2)).Adj
      (triHexPlanarFiniteStarToHexBuffered n x) c)
    (hc : c ∉ Set.range (triHexPlanarFiniteStarToHexBuffered n)) :
    triHexPlanarFiniteStarBoundary n x := by
  apply (triHexPlanarFiniteStar_boundary_iff_ambient n x).2
  refine ⟨c.1, hadj, ?_⟩
  rintro ⟨z, hz⟩
  apply hc
  refine ⟨z, Subtype.ext hz⟩

theorem triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict
    (n : Nat) :
    triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1) ⊆
      ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹'
        triHexPlanarFiniteStarRootBoundaryEvent n := by
  simpa only [triHexPlanarHexWhiteBufferedRootBoundaryEvent,
    triHexPlanarFiniteStarRootBoundaryEvent,
    triHexPlanarFiniteStarToHexBuffered_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triHexPlanarFiniteStarGraph n)
      (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n)
      (triHexPlanarFiniteStarBoundary n)
      (hexagonal.bufferedBoundary (n + 2))
      (triHexPlanarFiniteStarToHexBuffered_adjMatch n)
      (triHexPlanarFiniteStarToHexBuffered_not_boundary n)
      (triHexPlanarFiniteStarToHexBuffered_cross_boundary n)
      (triHexPlanarFiniteStarRoot n)

theorem triHexPlanarHexBufferedToFiniteStar_root (n : Nat) :
    triHexPlanarHexBufferedToFiniteStar (n + 1)
        (triHexPlanarHexWhiteBufferedRoot n) =
      triHexPlanarFiniteStarRoot
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) := by
  apply (triHexPlanarFiniteStarVertexEmbedding
    (triHexPlanarHexBufferedOuterStarLevel (n + 1))).injective
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq,
    triHexPlanarFiniteStarRoot_embedding]
  rfl

theorem triHexPlanarHexBufferedToFiniteStar_cross_boundary
    (n : Nat) (x : hexagonal.BufferedVertex n)
    (c : TriHexPlanarFiniteStarVertex
      (triHexPlanarHexBufferedOuterStarLevel n))
    (hadj : (triHexPlanarFiniteStarGraph
      (triHexPlanarHexBufferedOuterStarLevel n)).Adj
        (triHexPlanarHexBufferedToFiniteStar n x) c)
    (hc : c ∉ Set.range (triHexPlanarHexBufferedToFiniteStar n)) :
    hexagonal.bufferedBoundary n x := by
  refine ⟨triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n) c, ?_, ?_⟩
  · rw [← triHexPlanarHexBufferedToFiniteStar_embedding_eq n x]
    exact triHexPlanarFiniteStarGraph_adj_hexagonal _ hadj
  · intro hw
    apply hc
    let z : hexagonal.BufferedVertex n :=
      ⟨triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n) c, hw⟩
    refine ⟨z, ?_⟩
    apply (triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n)).injective
    rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq]

theorem triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict
    (n : Nat) :
    triHexPlanarFiniteStarRootBoundaryEvent
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) ⊆
      ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar (n + 1)) ⁻¹'
        triHexPlanarHexWhiteBufferedRootBoundaryEvent n := by
  simpa only [triHexPlanarHexWhiteBufferedRootBoundaryEvent,
    triHexPlanarFiniteStarRootBoundaryEvent,
    triHexPlanarHexBufferedToFiniteStar_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (hexagonal.bufferedGraph (n + 1))
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
      (triHexPlanarHexBufferedToFiniteStar (n + 1))
      (hexagonal.bufferedBoundary (n + 1))
      (triHexPlanarFiniteStarBoundary
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
      (triHexPlanarHexBufferedToFiniteStar_adjMatch (n + 1))
      (triHexPlanarHexBufferedToFiniteStar_not_boundary (n + 1))
      (triHexPlanarHexBufferedToFiniteStar_cross_boundary (n + 1))
      (triHexPlanarHexWhiteBufferedRoot n)

theorem triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass
    (n : Nat) {p q : Real} :
    triHexPlanarFiniteStarWiredBoundaryProbability n p q =
      finiteWiredEventMass (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarRootBoundaryEvent n) := by
  classical
  unfold triHexPlanarFiniteStarWiredBoundaryProbability
    finiteWiredEventMass
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold triHexPlanarFiniteStarBoundaryReachIndicator
  have hgraph := openSub_extendActive_restrictActive_eq
    (triHexPlanarFiniteStarGraph n) omega
  have hiff : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n)
          (restrictActive (triHexPlanarFiniteStarGraph n) omega))).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y)) ↔
    ∃ y, triHexPlanarFiniteStarBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n) omega).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) y := by
    rw [hgraph]
    constructor
    · rintro ⟨y, hy, hreach⟩
      exact ⟨Sum.inr y, hy, hreach⟩
    · rintro ⟨y, hy, hreach⟩
      rcases y with z | y
      · exact hy.elim
      · exact ⟨y, hy, hreach⟩
  have hiff' : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n)
          (restrictActive (triHexPlanarFiniteStarGraph n) omega))).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y)) ↔
      omega ∈ triHexPlanarFiniteStarRootBoundaryEvent n := by
    rw [hiff]
    rfl
  rw [if_congr hiff' rfl rfl]
  simp only [Set.indicator]


theorem triHexPlanarHexWhiteBuffered_mass_le_star
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1)) ≤
      triHexPlanarFiniteStarWiredBoundaryProbability n p q := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1)) ≤
      finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹'
          triHexPlanarFiniteStarRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict n)
    _ ≤ finiteWiredEventMass (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarRootBoundaryEvent n) := by
      simpa only [finiteWiredEventMass] using
        triHexPlanarFiniteStar_outerBuffered_dominated n hp hp1 hq
          (finiteRootBoundaryEvent_isIncreasing _ _ _)


theorem triHexPlanarFiniteStar_le_hexWhiteBuffered_mass
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexPlanarFiniteStarWiredBoundaryProbability
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q ≤
      finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) p q
        (triHexPlanarFiniteStarRootBoundaryEvent
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) ≤
      finiteWiredEventMass
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) p q
        (ocd_innerRestrict
          (triHexPlanarHexBufferedToFiniteStar (n + 1)) ⁻¹'
          triHexPlanarHexWhiteBufferedRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict n)
    _ ≤ finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) := by
      simpa only [finiteWiredEventMass] using
        triHexPlanarHexBuffered_outerStar_dominated (n + 1) hp hp1 hq
          (finiteRootBoundaryEvent_isIncreasing _ _ _)

theorem triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary
    (n : Nat) :
    triHexPlanarHexWhiteBufferedRootBoundaryEvent n =
      hexagonal.bufferedSetBoundaryEvent
        ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1) := by
  ext eta
  constructor
  · rintro ⟨y, hy, hreach⟩
    exact ⟨triHexPlanarHexWhiteBufferedRoot n, Set.mem_singleton _,
      y, hy, hreach⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    have hx' : x = triHexPlanarHexWhiteBufferedRoot n := by
      apply Subtype.ext
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact ⟨y, hy, hreach⟩

theorem triHexPlanarHexWhiteBuffered_eventMass_eq_measure
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) =
      (hexagonal.wiredBufferedMeasure (n + 1) hp hp1 hq :
        Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (n + 1)
          (hexagonal.bufferedSetBoundaryEvent
            ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1))) := by
  rw [hexagonal.wiredBufferedMeasure_real_cylinder (le_refl (n + 1))
    hp hp1 hq]
  unfold finiteWiredEventMass
  rw [triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary]
  apply Finset.sum_congr rfl
  intro omega _
  rfl

theorem triHexPlanarHexWhiteBuffered_eventMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)) atTop
      (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
          (hexagonal.setHitsInfinite
            ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
  have hdiag := hexagonal.wiredBufferedSetBoundary_diag_tendsto
    ({triHexPlanarHexWhiteRoot} : Set HexVertex) (Set.finite_singleton _)
    1 (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (triHexPlanarHexWhiteBufferedRoot 0).2)
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with n
  rw [triHexPlanarHexWhiteBuffered_eventMass_eq_measure n hp hp1
    (zero_lt_one.trans_le hq)]
  rw [Nat.one_add]

theorem triHexPlanarHexStarCofinalLevel_tendsto :
    Tendsto (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1))
      atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  unfold triHexPlanarHexBufferedOuterStarLevel
  exact Nat.add_lt_add_right
    (hexagonal.bufferedRadius_strictMono
      (Nat.add_lt_add_right (Nat.add_lt_add_right hab 1) 1)) 1


theorem triHexPlanarFiniteStar_cofinal_tendsto_hexWhiteInfinite
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => triHexPlanarFiniteStarWiredBoundaryProbability
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q) atTop
      (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
          (hexagonal.setHitsInfinite
            ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
  let c := fun n => finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1)) p q
    (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)
  have hc := triHexPlanarHexWhiteBuffered_eventMass_tendsto hp hp1 hq
  have hindex : Tendsto
      (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)
      atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      triHexPlanarHexStarCofinalLevel_tendsto
  have hlo : Tendsto
      (fun n => c (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1))
      atTop _ := hc.comp hindex
  have hhi : Tendsto c atTop _ := hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards with n
    exact triHexPlanarHexWhiteBuffered_mass_le_star
      (triHexPlanarHexBufferedOuterStarLevel (n + 1)) hp hp1 hq
  · filter_upwards with n
    exact triHexPlanarFiniteStar_le_hexWhiteBuffered_mass n hp hp1 hq


theorem triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) (w : Site 2)
    (hvw : triangularGraph.Adj v.1 w)
    (hw : w ∉ triHexPlanarFiniteTerminalFinset n) :
    triHexPlanarFiniteBoundary n v := by
  let e : triangularGraph.edgeSet := ⟨s(v.1, w), by
    rwa [SimpleGraph.mem_edgeSet]⟩
  let a := triangularEdgeChartEquiv.symm e
  rcases hpair : triHexPlanarTriangleIndexEquiv.symm a with ⟨z, i⟩
  have ha : triHexPlanarTriangleIndexEquiv (z, i) = a := by
    rw [← hpair]
    exact triHexPlanarTriangleIndexEquiv.apply_symm_apply a
  have hchart : triangularIndexedEdge a = s(v.1, w) :=
    congrArg Subtype.val (triangularEdgeChartEquiv.apply_symm_apply e)
  have hedge :
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) =
          s(v.1, w) := by
    rw [← hchart, ← ha]
    exact (triangularIndexedEdge_rebase_eq_cellEdge z i).symm
  have hz : z ∉ box 2 n := by
    intro hz
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨_, hwEq⟩ | ⟨hwEq, _⟩
    · apply hw
      apply Finset.mem_image.mpr
      exact ⟨(z, triHexTriangleEdgeTerminal2 i),
        Finset.mem_product.mpr ⟨by simpa using hz, Finset.mem_univ _⟩, hwEq⟩
    · apply hw
      apply Finset.mem_image.mpr
      exact ⟨(z, triHexTriangleEdgeTerminal1 i),
        Finset.mem_product.mpr ⟨by simpa using hz, Finset.mem_univ _⟩, hwEq⟩
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hv, _⟩ | ⟨_, hv⟩
  · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
    change v.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
    rw [← hv]
    simpa [triHexPlanarCellTerminal] using hz
  · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
    change v.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
    rw [← hv]
    simpa [triHexPlanarCellTerminal] using hz

end
end StatMech.FK.PeriodicPlanar
