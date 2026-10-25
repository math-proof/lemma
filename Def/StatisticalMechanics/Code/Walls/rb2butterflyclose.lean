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
import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose
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

def rb2_Cz (x y w : Bool) : ℤ :=
  match x, y, w with
  | false, false, false => 1
  | false, false, true  => 0
  | false, true,  false => 0
  | false, true,  true  => 1
  | true,  false, false => -1
  | true,  false, true  => 1
  | true,  true,  false => 2
  | true,  true,  true  => -1

def rb2_C (x y w : Bool) : ℝ := (rb2_Cz x y w : ℝ)

end rb2_part6
end StatMech.Walls.Reimer
