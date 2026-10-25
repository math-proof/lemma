/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part4
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Extension.Linear
import Def.StatisticalMechanics.Code.Walls.rb2butterflyclose
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unnecessarySeqFocus false

set_option linter.unusedSimpArgs false

set_option linter.unusedFintypeInType false

set_option maxHeartbeats 1200000


section rb2_part6

open Matrix

open Classical

lemma rb2_g2_decomp (x y z : Bool) :
    rbt_g2 x y z = ∑ w : Bool, rb2_C x y w * rbt_g2 false w z := by
  simp only [rb2_C, rb2_Cz, Fintype.sum_bool]
  cases x <;> cases y <;> cases z <;> simp [rbt_g2] <;> norm_num

end rb2_part6
end StatMech.Walls.Reimer
