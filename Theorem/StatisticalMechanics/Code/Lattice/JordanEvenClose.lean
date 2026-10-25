/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Def.StatisticalMechanics.Code.Lattice.JordanEvenClose
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jce_horizBelow_mk (a b : ℤ) (x y : Site 2) :
    jce_horizBelow a b s(x, y) ↔
      (x 1 = y 1) ∧ (x 1 ≤ b) ∧ ((x 0 = a ∧ y 0 = a + 1) ∨ (x 0 = a + 1 ∧ y 0 = a)) :=
  Iff.rfl

end Lattice
end StatMech
