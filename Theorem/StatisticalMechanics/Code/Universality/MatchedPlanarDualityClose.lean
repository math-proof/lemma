/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mpd_rot90Inv_rect (a b c d : ℤ) (x : Site 2) :
    x ∈ rect a b c d ↔ rot90Inv x ∈ rect c d (-b) (-a) := by
  simp only [mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem mpd_rot90Inv_bottomSide (a b c d : ℤ) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ rot90Inv x ∈ leftSide c d (-b) (-a) := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem mpd_rot90Inv_topSide (a b c d : ℤ) (x : Site 2) :
    x ∈ topSide a b c d ↔ rot90Inv x ∈ rightSide c d (-b) (-a) := by
  simp only [mem_topSide, mem_rightSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


end Universality
end StatMech
