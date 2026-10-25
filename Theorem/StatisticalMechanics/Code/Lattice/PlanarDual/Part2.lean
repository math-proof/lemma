/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part2
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem rot90Fun_apply (a b : ℤ) : rot90Fun ![a, b] = ![-b, a] := by
  funext i; fin_cases i <;> simp [rot90Fun]

@[simp] theorem rot90Inv_apply (a b : ℤ) : rot90Inv ![a, b] = ![b, -a] := by
  funext i; fin_cases i <;> simp [rot90Inv]


end Lattice
end StatMech
