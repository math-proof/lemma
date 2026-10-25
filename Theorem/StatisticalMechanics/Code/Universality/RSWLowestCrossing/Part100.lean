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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part98
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mixedWiredConnectorEvent_isIncreasing {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    IsIncreasing (rlc_mixedWiredConnectorEvent G) := by
  intro omega omega' hle hconn
  exact StatMech.TwoDim.connectedWithin_mono
    (rlc_wiredConnectorConfig_mono gamma gamma'
      (rlc_mixedAxisGapEdges G) hle) hconn

theorem rlc_mixedWiredConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_mixedWiredConnectorEvent G).indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hcfg := rlc_wiredConnectorConfig_congr gamma gamma'
    (rlc_mixedAxisGapEdges G) hagree
  have hevent : omega ∈ rlc_mixedWiredConnectorEvent G ↔
      omega' ∈ rlc_mixedWiredConnectorEvent G := by
    simp only [rlc_mixedWiredConnectorEvent, Set.mem_setOf_eq, hcfg]
  by_cases hmem : omega ∈ rlc_mixedWiredConnectorEvent G
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

theorem rlc_mixedWiredConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_mixedWiredConnectorEvent G) :=
  measurableSet_of_dependsOn (rlc_mixedWiredConnectorEvent_dependsOn G)


theorem rlc_mixedWiredConnector_half_of_dual_reflection {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_connector_half_of_dual_reflection rba_selfDualMeasure
    rlc_dualReflectConfig rlc_dualReflectConfig_measurePreserving
    (rlc_mixedWiredConnectorEvent G)
    (rlc_mixedWiredConnectorEvent_measurableSet G)
  intro omega hno
  exact hdual omega hno


theorem rlc_mixedWiredConnector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedWiredConnectorEvent G ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hwire⟩ := homega
  have hconn : ConnectedWithin 2 omega
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex,
        rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right⟩
      ⟨G.upperVertex,
        rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_wiredConnectorConfig_le_of_pathOpen
        gamma gamma' (rlc_mixedAxisGapEdges G) omega hgamma hgamma') hwire
  obtain ⟨_hlowerSmall, hlowerRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma G.lowerVertex_mem_right
  obtain ⟨_hupperSmall, hleftUpperSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' G.upperVertex_mem_left
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
  have hlowerRight := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hrightSub hlowerRightSmall
  have hleftUpper := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hleftSub hleftUpperSmall
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
  exact hleftUpper.trans (hconn.symm.trans hlowerRight)


theorem rlc_wiredConnectorConfig_rightPathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_wiredConnectorConfig gamma gamma' U omega ∈
      rlc_pathOpen gamma.1 := by
  intro e he
  simp [rlc_wiredConnectorConfig, he]

theorem rlc_wiredConnectorConfig_leftPathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_wiredConnectorConfig gamma gamma' U omega ∈
      rlc_pathOpen gamma'.1 := by
  intro e he
  simp [rlc_wiredConnectorConfig, he]


theorem rlc_maskConfig_le_wiredConnectorConfig {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_maskConfig U omega ≤
      rlc_wiredConnectorConfig gamma gamma' U omega := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 <;>
    simp [rlc_wiredConnectorConfig, hp]


theorem rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_mixedAxisGapConnectorEvent G ⊆
      rlc_mixedWiredConnectorEvent G := by
  intro omega hconn
  obtain ⟨x, hxPath, y, hyPath, hxR, hyR, hxyMask⟩ := hconn
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hrightOpen : eta ∈ rlc_pathOpen gamma.1 :=
    rlc_wiredConnectorConfig_rightPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  have hleftOpen : eta ∈ rlc_pathOpen gamma'.1 :=
    rlc_wiredConnectorConfig_leftPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hlowerR, hstartLower⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen
      G.lowerVertex_mem_right
  obtain ⟨_hxSmall, hstartX⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen hxPath
  obtain ⟨_hySmall, hleftStartY⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen hyPath
  obtain ⟨hupperR, hleftStartUpper⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen
      G.upperVertex_mem_left
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
  have hlowerFull : G.lowerVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right
  have hupperFull : G.upperVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left
  have hlowerX : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex, hlowerFull⟩ ⟨x, hxR⟩ := by
    simpa only using
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hrightSub
        hstartLower).symm.trans
          (StatMech.RSW.Strip.connectedWithin_mono_set eta hrightSub hstartX)
  have hyUpper : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨y, hyR⟩ ⟨G.upperVertex, hupperFull⟩ := by
    simpa only using
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hleftSub
        hleftStartY).symm.trans
          (StatMech.RSW.Strip.connectedWithin_mono_set eta hleftSub
            hleftStartUpper)
  have hxy : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_maskConfig_le_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega) hxyMask
  exact hlowerX.trans (hxy.trans hyUpper)


end Universality
end StatMech
