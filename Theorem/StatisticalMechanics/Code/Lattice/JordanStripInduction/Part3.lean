/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Structure.StatisticalMechanics.Code.Lattice.JordanStripInduction
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_col_consecutive {P : Set (Site 2)} {m m' c d : ℤ} (A : JsiRowArc P m m' c d)
    (r s : ℤ) (hr : c ≤ r) (hrd : r ≤ d) (hs : c ≤ s) (hsd : s ≤ d)
    (hrs : r - s = 1 ∨ r - s = -1) :
    -1 ≤ A.col r - A.col s ∧ A.col r - A.col s ≤ 1 := by
  rcases hrs with h | h
  · have hse : s + 1 = r := by omega
    have hsh := A.shift s hs (by omega); rw [hse] at hsh; omega
  · have hre : r + 1 = s := by omega
    have hsh := A.shift r hr (by omega); rw [hre] at hsh; omega


end Lattice
end StatMech
