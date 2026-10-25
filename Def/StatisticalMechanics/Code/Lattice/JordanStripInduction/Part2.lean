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
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part3
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def jsi_leftRegion (col : ℤ → ℤ) (α β c d : ℤ) : Set (Site 2) :=
  {z | z ∈ rect α β c d ∧ z 0 ≤ col (z 1)}

end Lattice
end StatMech
