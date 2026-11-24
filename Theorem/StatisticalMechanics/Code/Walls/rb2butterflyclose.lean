module
public import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part4
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.Extension.Linear
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unnecessarySeqFocus false

set_option linter.unusedSimpArgs false

set_option linter.unusedFintypeInType false

set_option maxHeartbeats 1200000


theorem rb2_finrank_Q (m : ℕ) :
    Module.finrank ℝ (rbt_Q m → ℝ) = 2 ^ m := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [rbt_Q, Fintype.card_fin]


end StatMech.Walls.Reimer
