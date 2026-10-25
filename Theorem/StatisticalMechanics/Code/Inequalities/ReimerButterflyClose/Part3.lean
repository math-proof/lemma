/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


section Weighted

variable [Fintype α]


lemma fwt_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (S : Finset α) : 0 ≤ fwt w S :=
  Finset.prod_nonneg (fun x _ => hw x _)


lemma fwt'_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α) (S : Finset α) :
    0 ≤ fwt' w i S :=
  Finset.prod_nonneg (fun x _ => hw x _)


lemma fwt_of_mem (w : α → Bool → ℝ) {S : Finset α} {i : α} (hi : i ∈ S) :
    fwt w S = w i true * fwt' w i (S.erase i) := by
  unfold fwt fwt'
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [decide_eq_true (by simpa using hi : i ∈ S), mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [Finset.mem_erase] at hx
  congr 1
  simp [Finset.mem_erase, hx.1]


lemma fwt_of_notMem (w : α → Bool → ℝ) {S : Finset α} {i : α} (hi : i ∉ S) :
    fwt w S = w i false * fwt' w i S := by
  unfold fwt fwt'
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [decide_eq_false (by simpa using hi : i ∉ S)]
  ring


end Weighted
end StatMech
