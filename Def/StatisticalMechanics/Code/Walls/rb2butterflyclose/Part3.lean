module
public import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part4
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.Extension.Linear
public import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part3
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


section rb2_part6

open Matrix

open Classical

noncomputable def rb2_M2 {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Matrix T T (ZMod 2) :=
  fun y z => ∏ i, ((rb2_Cz (body (y : rbt_Q m) i) ((y : rbt_Q m) i) ((z : rbt_Q m) i) : ZMod 2))


noncomputable def rb2_blab {m : ℕ} (T : Finset (rbt_Q m)) : T → LinearExtension (rbt_Q m) :=
  fun y => toLinearExtension (y : rbt_Q m)

end rb2_part6
end StatMech.Walls.Reimer
