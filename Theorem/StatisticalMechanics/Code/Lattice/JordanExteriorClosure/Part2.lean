/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_rayEdge_mk (z x y : Site 2) :
    jec_rayEdge z s(x, y) ↔
      (x 0 = y 0 ∧ x 0 ≤ z 0 - 1) ∧
      ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (y 1 = z 1 - 1 ∧ x 1 = z 1)) := by
  unfold jec_rayEdge; rfl


end Lattice
end StatMech
