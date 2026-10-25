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
import Def.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part2
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

lemma rb2_g_decomp {m : ℕ} (x y : rbt_Q m) :
    rbt_g x y = ∑ z : rbt_Q m, (∏ i, rb2_C (x i) (y i) (z i)) • rb2_hbasis z := by
  funext w
  simp only [rb2_hbasis, rbt_g, rbt_tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hL : ∀ i, rbt_g2 (x i) (y i) (w i)
      = ∑ zi : Bool, rb2_C (x i) (y i) zi * rbt_g2 false zi (w i) := fun i => rb2_g2_decomp _ _ _
  rw [Finset.prod_congr rfl (fun i _ => hL i)]
  rw [Fintype.prod_sum (fun i (zi : Bool) => rb2_C (x i) (y i) zi * rbt_g2 false zi (w i))]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.prod_mul_distrib]


lemma rb2_hbasis_off {m : ℕ} (z w : rbt_Q m) (h : ¬ w ≤ z) : rb2_hbasis z w = 0 := by
  simp only [rb2_hbasis, rbt_g, rbt_tens]
  rw [Pi.le_def, not_forall] at h
  obtain ⟨i, hi⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  
  have : z i = false ∧ w i = true := by
    cases hz : z i <;> cases hw : w i <;> simp_all [Bool.le_iff_imp]
  rw [this.1, this.2]; simp [rbt_g2]

lemma rb2_hbasis_diag {m : ℕ} (z : rbt_Q m) : rb2_hbasis z z ≠ 0 := by
  simp only [rb2_hbasis, rbt_g, rbt_tens]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases hz : z i <;> simp [rbt_g2]

lemma rb2_hbasis_indep (m : ℕ) : LinearIndependent ℝ (fun z : rbt_Q m => rb2_hbasis z) := by
  have h := rbt_triangular_indep
    (ι := (rbt_Q m)ᵒᵈ)
    (M := fun z w => rb2_hbasis (OrderDual.ofDual z) (OrderDual.ofDual w))
    (fun z w hzw => rb2_hbasis_off _ _ (by simpa [OrderDual.toDual_le_toDual] using hzw))
    (fun z => rb2_hbasis_diag _)
  exact h


lemma rb2_Cz_off (x y w : Bool) (h : ¬ y ≤ w) : ((rb2_Cz x y w : ZMod 2)) = 0 := by
  
  have hyw : y = true ∧ w = false := by cases hy:y <;> cases hw:w <;> simp_all [Bool.le_iff_imp]
  obtain ⟨hy, hw⟩ := hyw; subst hy; subst hw
  cases x <;> decide

lemma rb2_Cz_diag (x y : Bool) : ((rb2_Cz x y y : ZMod 2)) = 1 := by
  cases x <;> cases y <;> decide


end rb2_part6
end StatMech.Walls.Reimer
