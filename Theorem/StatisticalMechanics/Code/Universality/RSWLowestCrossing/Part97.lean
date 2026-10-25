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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part95
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mixedAxisGapConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_mixedAxisGapConnectorEvent G).indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) :=
  rlc_supportConnectorEvent_dependsOn gamma gamma'
    (rlc_mixedAxisGapEdges G)

theorem rlc_mixedAxisGapConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_mixedAxisGapConnectorEvent G) :=
  rlc_supportConnectorEvent_measurableSet gamma gamma'
    (rlc_mixedAxisGapEdges G)


theorem rlc_supportConnector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_supportConnectorEvent gamma gamma' U ⊆
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
    StatMech.TwoDim.connectedWithin_mono (rlc_maskConfig_le U omega) hxyMask
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

theorem rlc_mixedAxisGapConnector_glues_horizontal (n : ℤ) (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedAxisGapConnectorEvent G ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n :=
  rlc_supportConnector_glues_horizontal n hn gamma gamma'
    (rlc_mixedAxisGapEdges G)


end Universality
end StatMech
