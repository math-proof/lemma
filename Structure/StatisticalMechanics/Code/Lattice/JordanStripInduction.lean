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
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part2
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


structure JsiRowArc (P : Set (Site 2)) (m m' c d : ℤ) where
  
  col : ℤ → ℤ
  
  band_lo : ∀ r, c ≤ r → r ≤ d → m ≤ col r
  
  band_hi : ∀ r, c ≤ r → r ≤ d → col r ≤ m'
  
  shift : ∀ r, c ≤ r → r < d →
    col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1
  
  on_arc : ∀ z : Site 2, c ≤ z 1 → z 1 ≤ d → z 0 = col (z 1) → m ≤ z 0 → z 0 ≤ m' → z ∈ P


end Lattice
end StatMech
