/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part78
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_connectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_connectorEvent gamma gamma').indicator (fun _ => (1 : ℝ)))
      (rlc_connectorEdges gamma gamma' : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hmask : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega =
      rlc_maskConfig (rlc_connectorEdges gamma gamma') omega' :=
    rlc_maskConfig_congr hagree
  have hevent : omega ∈ rlc_connectorEvent gamma gamma' ↔
      omega' ∈ rlc_connectorEvent gamma gamma' := by
    simp only [rlc_connectorEvent, Set.mem_setOf_eq, hmask]
  by_cases hmem : omega ∈ rlc_connectorEvent gamma gamma'
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

theorem rlc_connectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_connectorEvent gamma gamma') :=
  measurableSet_of_dependsOn (rlc_connectorEvent_dependsOn gamma gamma')

theorem rlc_maskConfig_le (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) : rlc_maskConfig U omega ≤ omega := by
  intro e
  by_cases he : e ∈ U
  · simp [rlc_maskConfig, he]
  · simp [rlc_maskConfig, he]


theorem rlc_pathOpen_connected_start {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega ∈ rlc_pathOpen gamma)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma) :
    ∃ hzR : z ∈ rect a b c d,
      ConnectedWithin 2 omega (rect a b c d)
        ⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩ ⟨z, hzR⟩ := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let q := gamma.2.2.1.takeUntil zs hzs
  have hqopen : ∀ e ∈ q.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true := by
    intro e he
    simp only [Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    apply hopen
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨e0, gamma.2.2.1.edges_takeUntil_subset hzs he0, rfl⟩
  exact ⟨zs.2, ⟨rlc_openWalkOfEdges omega q hqopen⟩⟩

theorem rlc_pathOpen_connected_finish {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega ∈ rlc_pathOpen gamma)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma) :
    ∃ hzR : z ∈ rect a b c d,
      ConnectedWithin 2 omega (rect a b c d) ⟨z, hzR⟩
        ⟨(gamma.2.1 : Site 2), rightSide_subset gamma.2.1.2⟩ := by
  obtain ⟨hzR, hstart⟩ := rlc_pathOpen_connected_start gamma omega hopen hz
  have hfull : ConnectedWithin 2 omega (rect a b c d)
      ⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩
      ⟨(gamma.2.1 : Site 2), rightSide_subset gamma.2.1.2⟩ := by
    refine ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩
    intro e he
    exact hopen e (by simpa only [rlc_pathEdges] using he)
  exact ⟨hzR, hstart.symm.trans hfull⟩


theorem rlc_connector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_connectorEvent gamma gamma' ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hconn⟩ := homega
  obtain ⟨x, hxg, y, hyg, hxR, hyR, hxyMask⟩ := hconn
  obtain ⟨_hxSmall, hxToRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma hxg
  obtain ⟨_hySmall, hleftToYSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' hyg
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hxToRight := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hrightSub hxToRightSmall
  have hleftToY := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hleftSub hleftToYSmall
  have hxy : ConnectedWithin 2 omega (rect (-2 * n) (2 * n) (-n) n)
      ⟨x, hxR⟩ ⟨y, hyR⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_maskConfig_le (rlc_connectorEdges gamma gamma') omega) hxyMask
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftToY.trans (hxy.symm.trans hxToRight)

theorem rlc_originRegion_not_barrier {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma') :
    z ∉ rlc_connectorBarrier gamma gamma' := by
  have hzset : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, _ho, _hreach⟩ := hzset
  exact (Finset.mem_sdiff.mp hzAllowed).2

theorem rlc_rightPathEdges_disjoint_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma.1) (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e hePath heConnector
  simp only [rlc_connectorEdges, Finset.mem_filter] at heConnector
  obtain ⟨_zbox, z, hzRegion, hze⟩ := heConnector
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.1])
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.2])

theorem rlc_leftPathEdges_disjoint_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e hePath heConnector
  simp only [rlc_connectorEdges, Finset.mem_filter] at heConnector
  obtain ⟨_zbox, z, hzRegion, hze⟩ := heConnector
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hePath
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.1])
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.2])


theorem rlc_rightPathVertex_mem_connectorBox {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzsmall := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzsmall ⊢
  omega

theorem rlc_leftPathVertex_mem_connectorBox {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzsmall := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzsmall ⊢
  omega


theorem rlc_mem_connectorEvent_of_common_vertex {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1)
    (hz' : z ∈ rlc_pathVertices gamma'.1) :
    omega ∈ rlc_connectorEvent gamma gamma' := by
  let hzR := rlc_rightPathVertex_mem_connectorBox gamma hz
  let hzR' := rlc_leftPathVertex_mem_connectorBox gamma' hz'
  refine ⟨z, hz, z, hz', hzR, hzR', ?_⟩
  simpa only using
    (connectedWithin_refl
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨z, hzR⟩)


theorem rlc_pathVertices_disjoint_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hno (rlc_mem_connectorEvent_of_common_vertex gamma gamma' omega hz hz')


theorem rlc_axis_endpoints_strict_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, by simpa [x] using leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, by simpa [y] using rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hxy : x ≠ y := by
    intro h
    exact (Finset.disjoint_left.mp
      hdisj) hxPath (by simpa [h] using hyPath)
  have hx0 : x 0 = 0 := by simpa only [x] using gamma.1.1.2.2
  have hy0 : y 0 = 0 := by simpa only [y] using gamma'.1.2.1.2.2
  have hxy1 : x 1 ≠ y 1 := by
    intro h1
    apply hxy
    funext i
    fin_cases i
    · exact hx0.trans hy0.symm
    · exact h1
  have hxLower : x 1 ≤ 0 := gamma.2.1
  have hyUpper : 0 ≤ y 1 := gamma'.2.2
  change x 1 < y 1
  omega


theorem rlc_axis_endpoints_strict_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 :=
  rlc_axis_endpoints_strict_of_disjoint gamma gamma'
    (rlc_pathVertices_disjoint_of_not_connector gamma gamma' omega hno)


theorem rlc_exists_axis_barrier_gap_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    ∃ a b : ℤ,
      a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧
      b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧
      (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧
      b ≤ (gamma'.1.2.1 : Site 2) 1 ∧
      ∀ t : ℤ, a < t → t < b →
        ![0, t] ∉ rlc_connectorBarrier gamma gamma' := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, by simpa [x] using leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, by simpa [y] using rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hx0 : x 0 = 0 := by simpa only [x] using gamma.1.1.2.2
  have hy0 : y 0 = 0 := by simpa only [y] using gamma'.1.2.1.2.2
  have hxAxis : x 1 ∈ rlc_axisHeights (rlc_pathVertices gamma.1) := by
    rw [rlc_mem_axisHeights_iff]
    have hvec : ![0, x 1] = x := by
      funext i
      fin_cases i <;> simp [hx0]
    simpa [hvec] using hxPath
  have hyAxis : y 1 ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) := by
    rw [rlc_mem_axisHeights_iff]
    have hvec : ![0, y 1] = y := by
      funext i
      fin_cases i <;> simp [hy0]
    simpa [hvec] using hyPath
  have hxy : x 1 < y 1 := by
    simpa only [x, y] using
      rlc_axis_endpoints_strict_of_disjoint gamma gamma' hdisj
  obtain ⟨a, b, ha, hb, hxa, hab, hby, hgap⟩ :=
    rlc_exists_finset_gap
      (rlc_axisHeights (rlc_pathVertices gamma.1))
      (rlc_axisHeights (rlc_pathVertices gamma'.1)) hxAxis hyAxis hxy
  refine ⟨a, b, ha, hb, hxa, hab, hby, ?_⟩
  intro t hat htb hbarrier
  obtain ⟨htA, htB⟩ := hgap t hat htb
  rw [rlc_axis_mem_connectorBarrier_iff] at hbarrier
  rcases hbarrier with hbarrier | hbarrier
  · exact htA ((rlc_mem_axisHeights_iff _ _).2 hbarrier)
  · exact htB ((rlc_mem_axisHeights_iff _ _).2 hbarrier)


end Universality
end StatMech
