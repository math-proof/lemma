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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part30
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftTopSide_subset_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    topSide (-2 * n) 0 (-n) n ⊆ rlc_aboveSet hn gamma := by
  intro z hz
  exact (rlc_swappedLeftBelowSet_spec hn gamma).2.1 (crf_swap z)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hz.1)
    (by simpa using hz.2)

theorem rlc_leftBottomSide_disjoint_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n) (rlc_aboveSet hn gamma) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzAbove
  exact hzAbove ((rlc_swappedLeftBelowSet_spec hn gamma).1 (crf_swap z)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hzBottom.1)
    (by simpa using hzBottom.2))


theorem rlc_half_rightDiagonal_lower_bound (n : ℤ) (hn : 0 < n)
    (hH : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
  have h := rlc_rightDiagonal_lower_bound (2⁻¹ : ℝ≥0) half_le_one n hn
    ((1 : ℝ) / 2) (by norm_num) hH hV
  norm_num at h
  simpa [rba_selfDualMeasure] using h

theorem rlc_half_leftDiagonal_lower_bound (n : ℤ) (hn : 0 < n)
    (hH : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
  rw [rlc_leftDiagonal_prob_eq_right]
  exact rlc_half_rightDiagonal_lower_bound n hn hH hV


theorem rlc_lrRestricted_univ (a b c d : ℤ) :
    rlc_lrRestrictedEvent a b c d Set.univ Set.univ =
      horizontalCrossingEvent a b c d := by
  ext omega
  simp only [rlc_lrRestrictedEvent, Set.mem_setOf_eq, Set.mem_univ, true_and,
    mem_horizontalCrossingEvent, HorizontalCrossing]

theorem rlc_horizontalCrossing_dependsOn (a b c d : ℤ) :
    DependsOn ((horizontalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  rw [← rlc_lrRestricted_univ]
  exact rlc_lrRestrictedEvent_dependsOn a b c d Set.univ Set.univ

theorem rlc_horizontalCrossing_measurableSet (a b c d : ℤ) :
    MeasurableSet (horizontalCrossingEvent a b c d) :=
  measurableSet_of_dependsOn (rlc_horizontalCrossing_dependsOn a b c d)

theorem rlc_verticalCrossing_measurableSet (a b c d : ℤ) :
    MeasurableSet (verticalCrossingEvent a b c d) :=
  measurableSet_of_dependsOn (rlc_verticalCrossing_dependsOn a b c d)


theorem rlc_square_half (m : ℤ) (hm : 0 < m) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 m 0 m) := by
  exact crr_square_half m hm
    (rlc_horizontalCrossing_measurableSet 0 m 0 m)
    (by
      change MeasurableSet (verticalCrossingEvent 0 (m - 1) (-1) m)
      exact rlc_verticalCrossing_measurableSet 0 (m - 1) (-1) m)
    (rlc_horizontalCrossing_measurableSet (-1) m 0 (m - 1))

theorem rlc_centered_square_horizontal_half (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
  have hbase := rlc_square_half (2 * n) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n) 0 (2 * n) (![0, -n] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * n) 0 (2 * n))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) =
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 (2 * n)) := by
    simpa [show 2 * n + -n = n by ring] using htrans
  rwa [heq]

theorem rlc_centered_square_vertical_half (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n) := by
  have hH := rlc_centered_square_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap 0 (2 * n) (-n) n
    (rlc_horizontalCrossing_measurableSet (-n) n 0 (2 * n))
  have htrans := cti_horizontalCrossing_translation_invariant
    (-n) n 0 (2 * n) (![n, -n] : Site 2)
    (rlc_horizontalCrossing_measurableSet (-n) n 0 (2 * n))
  have heq : rba_selfDualMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n) =
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
    rw [hswap]
    simpa [show -n + n = 0 by ring, show n + n = 2 * n by ring,
      show 2 * n + -n = n by ring] using htrans.symm
  rwa [heq]

theorem rlc_half_rightDiagonal_unconditional (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) :=
  rlc_half_rightDiagonal_lower_bound n hn
    (rlc_centered_square_horizontal_half n hn)
    (rlc_centered_square_vertical_half n hn)

theorem rlc_half_leftDiagonal_unconditional (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 32 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
  rw [rlc_leftDiagonal_prob_eq_right]
  exact rlc_half_rightDiagonal_unconditional n hn


end Universality
end StatMech
