/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

noncomputable def wnd_signStep (z u v : Site 2) : ℤ := by
  classical
  exact
    if (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1 then 1
    else if (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1 then -1
    else 0


end Lattice
end StatMech
