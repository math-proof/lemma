/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ArcMonotonise
import Theorem.StatisticalMechanics.Code.Lattice.JordanConvexBox.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def JcbColShift (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Prop :=
  ∃ col : ℤ → ℤ,
    (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧
    (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧
    (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) ∧
    (∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ overlapComp ω m m' c d xB hxB) ∧
    col (c - 1) = col c ∧
    (∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1)


end Lattice
end StatMech
