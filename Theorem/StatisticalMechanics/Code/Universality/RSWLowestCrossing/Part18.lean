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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part18
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_translate_rightDiagonal_to_left (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n) :
    omega ∈ rlc_leftDiagonal n := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let xl : leftSide (-2 * n) 0 (-n) n :=
    ⟨(x : Site 2) + rlc_leftShift n,
      by simpa using
        (cti_mem_leftSide_translate 0 (2 * n) (-n) n (rlc_leftShift n) x).mp x.2⟩
  let yl : rightSide (-2 * n) 0 (-n) n :=
    ⟨(y : Site 2) + rlc_leftShift n,
      by simpa using
        (cti_mem_rightSide_translate 0 (2 * n) (-n) n (rlc_leftShift n) y).mp y.2⟩
  refine ⟨xl, yl, ?_, ?_, ?_⟩
  · simpa [xl, rlc_lowerHalf] using hx
  · simpa [yl, rlc_upperHalf] using hy
  · exact hxy.map (rlc_leftShiftHom n omega)

theorem rlc_translate_leftDiagonal_to_right (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : omega ∈ rlc_leftDiagonal n) :
    translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let xr : leftSide 0 (2 * n) (-n) n :=
    ⟨(x : Site 2) - rlc_leftShift n, by
      rw [cti_mem_leftSide_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
      simpa using x.2⟩
  let yr : rightSide 0 (2 * n) (-n) n :=
    ⟨(y : Site 2) - rlc_leftShift n, by
      rw [cti_mem_rightSide_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
      simpa using y.2⟩
  refine ⟨xr, yr, ?_, ?_, ?_⟩
  · simpa [xr, rlc_lowerHalf] using hx
  · simpa [yr, rlc_upperHalf] using hy
  · exact hxy.map (rlc_leftShiftHomInv n omega)

theorem rlc_leftDiagonal_preimage (n : ℤ) :
    translateConfig (rlc_leftShift n) ⁻¹' rlc_rightDiagonal n =
      rlc_leftDiagonal n := by
  ext omega
  exact ⟨rlc_translate_rightDiagonal_to_left n omega,
    rlc_translate_leftDiagonal_to_right n omega⟩

theorem rlc_leftDiagonal_prob_eq_right (n : ℤ) :
    rba_selfDualMeasure.real (rlc_leftDiagonal n) =
      rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
  rw [← rlc_leftDiagonal_preimage n]
  exact (cti_selfDual_shift_invariant (rlc_leftShift n)).measureReal_preimage
    (measurableSet_of_dependsOn
      (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
        rlc_lowerHalf rlc_upperHalf)).nullMeasurableSet


end Universality
end StatMech
