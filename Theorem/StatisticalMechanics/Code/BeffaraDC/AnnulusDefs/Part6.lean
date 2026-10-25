/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part6
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

@[simp] theorem diagReflEquiv_apply (x : Site 2) : diagReflEquiv x = diagReflFun x := rfl

@[simp] theorem diagReflEquiv_symm_apply (x : Site 2) :
    diagReflEquiv.symm x = diagReflFun x := rfl


theorem diagRefl_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (diagReflFun x) (diagReflFun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [diagReflFun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Nat.add_comm]


end BeffaraDC
end StatMech
