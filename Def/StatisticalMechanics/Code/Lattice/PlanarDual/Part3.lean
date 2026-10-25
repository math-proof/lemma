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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part2
open SimpleGraph


namespace StatMech

namespace Lattice

def rot90Equiv : Site 2 ≃ Site 2 where
  toFun := rot90Fun
  invFun := rot90Inv
  left_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]
  right_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]

end Lattice
end StatMech
