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
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part3
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem rot90Equiv_apply (x : Site 2) : rot90Equiv x = rot90Fun x := rfl

@[simp] theorem rot90Equiv_symm_apply (x : Site 2) : rot90Equiv.symm x = rot90Inv x := rfl


theorem rot90_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (rot90Fun x) (rot90Fun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rot90Fun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg, Nat.add_comm]


end Lattice
end StatMech
