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
import Def.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part4
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

lemma rb2_Mz_det_ne_zero {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_Mz body T).det ≠ 0 := by
  intro h
  
  have hmap : rb2_M2 body T = (rb2_Mz body T).map (Int.castRingHom (ZMod 2)) := by
    funext y z
    simp only [rb2_M2, rb2_Mz, Matrix.map_apply, Int.coe_castRingHom, Int.cast_prod]
  have : (rb2_M2 body T).det = ((rb2_Mz body T).det : ZMod 2) := by
    have hd := RingHom.map_det (Int.castRingHom (ZMod 2)) (rb2_Mz body T)
    rw [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd]; rfl
  rw [rb2_M2_det] at this
  rw [h] at this
  simp at this


end rb2_part6
end StatMech.Walls.Reimer
