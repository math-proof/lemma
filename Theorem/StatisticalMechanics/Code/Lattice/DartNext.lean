/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Def.StatisticalMechanics.Code.Lattice.DartNext
open SimpleGraph


namespace StatMech

namespace Lattice

theorem adj_iff_unitWt_sub (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔ unitWt (x - y) = 1 := by
  simp only [hypercubicLattice_adj, unitWt]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.sub_apply]


theorem unitWt_neg (z : Site 2) : unitWt (-z) = unitWt z := by
  unfold unitWt
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.neg_apply, Int.natAbs_neg]


theorem unitWt_rot90Fun (z : Site 2) : unitWt (rot90Fun z) = unitWt z := by
  unfold unitWt rot90Fun
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natAbs_neg]
  ring


theorem unitWt_dir (e : Dart) : unitWt e.dir = 1 := by
  have h := e.adj
  rw [adj_iff_unitWt_sub] at h
  rw [Dart.dir_def, ← unitWt_neg, neg_sub]
  exact h


theorem unitWt_rot90Fun_dir (e : Dart) : unitWt (rot90Fun e.dir) = 1 := by
  rw [unitWt_rot90Fun]; exact unitWt_dir e


theorem unitWt_neg_rot90Fun_dir (e : Dart) : unitWt (-rot90Fun e.dir) = 1 := by
  rw [unitWt_neg]; exact unitWt_rot90Fun_dir e


end Lattice
end StatMech
