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
import Def.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part3
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

lemma rb2_blab_inj {m : ℕ} (T : Finset (rbt_Q m)) : Function.Injective (rb2_blab T) := by
  intro a b h
  exact Subtype.ext (show (a : rbt_Q m) = (b : rbt_Q m) from h)

lemma rb2_M2_blockTri {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_M2 body T).BlockTriangular (rb2_blab T) := by
  intro y z hlt
  simp only [rb2_M2]
  have hlt' : (toLinearExtension (z : rbt_Q m)) < (toLinearExtension (y : rbt_Q m)) := hlt
  have hnle : ¬ (y : rbt_Q m) ≤ (z : rbt_Q m) := by
    intro hle
    exact absurd (toLinearExtension.monotone hle) (not_le.mpr hlt')
  rw [Pi.le_def, not_forall] at hnle
  obtain ⟨i, hi⟩ := hnle
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rb2_Cz_off _ _ _ hi)

lemma rb2_M2_det {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_M2 body T).det = 1 := by
  rw [(rb2_M2_blockTri body T).det]
  apply Finset.prod_eq_one
  intro a ha
  
  obtain ⟨y0, _, hy0⟩ := Finset.mem_image.mp ha
  haveI : Subsingleton {y // rb2_blab T y = a} := ⟨by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    exact Subtype.ext (rb2_blab_inj T (hp.trans hq.symm))⟩
  have hk : (⟨y0, hy0⟩ : {y // rb2_blab T y = a}) = (⟨y0, hy0⟩ : {y // rb2_blab T y = a}) := rfl
  rw [det_eq_elem_of_subsingleton _ (⟨y0, hy0⟩ : {y // rb2_blab T y = a})]
  simp only [toSquareBlock_def, rb2_M2, Matrix.of_apply]
  apply Finset.prod_eq_one
  intro i _
  exact rb2_Cz_diag _ _


end rb2_part6
end StatMech.Walls.Reimer
