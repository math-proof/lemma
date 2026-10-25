/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem fwr_sharedEdge_eq_crossEdge_horiz (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x + 1, y] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
  rw [sharedPrimalEdge_right]
  unfold faceCorner10 faceCorner11 rpc_crossEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero]; omega)]
  unfold rpc_hCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 2 <;>
    (funext i; fin_cases i <;>
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero] <;> omega)


theorem fwr_sharedEdge_eq_crossEdge_vert (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x, y + 1] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 1, y + 2] : Site 2) := by
  rw [sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11 rpc_crossEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega),
      if_neg (by simp only [Matrix.cons_val_zero]; omega),
      if_pos (by simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
  unfold rpc_vCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (x + 1 - 1 : ℤ) = x by ring]


end Walls
end StatMech
