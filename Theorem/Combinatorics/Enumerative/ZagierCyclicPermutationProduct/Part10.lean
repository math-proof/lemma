/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part10
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

@[simp]
theorem zagBlockMiddle_val {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockMiddle a b c hab hbc : ℕ) = a + (c - b) :=
  rfl

theorem zagBlockMiddle_bounds {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    a < zagBlockMiddle a b c hab hbc ∧
      zagBlockMiddle a b c hab hbc < c := by
  constructor <;> rw [Fin.lt_def] <;>
    simp only [zagBlockMiddle_val] <;> omega

theorem zagBlockMiddle_reverse {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockMiddle a (zagBlockMiddle a b c hab hbc) c
      (zagBlockMiddle_bounds a b c hab hbc).1
      (zagBlockMiddle_bounds a b c hab hbc).2 = b := by
  apply Fin.ext
  simp only [zagBlockMiddle_val]
  omega

theorem zagBlockSwap_apply_left {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc a = a := by
  apply Fin.ext
  simp [zagBlockSwapNat]

theorem zagBlockSwap_apply_middle {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc (zagBlockMiddle a b c hab hbc) = c := by
  apply Fin.ext
  change zagBlockSwapNat a b c (a + (c - b)) = c
  simp only [zagBlockSwapNat]
  split_ifs <;> omega

theorem zagBlockSwap_apply_right {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc c = b := by
  apply Fin.ext
  simp only [zagBlockSwap_val, zagBlockSwapNat]
  split_ifs <;> omega

theorem zagBlockSwap_symm_apply_middle {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm b = c := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_right]

theorem zagBlockSwap_symm_apply_left {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm a = a := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_left]

theorem zagBlockSwap_symm_apply_right {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm c =
      zagBlockMiddle a b c hab hbc := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_middle]

theorem zagBlockSwap_preserves_leftCut {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) :
    a ≤ zagBlockSwap a b c hab hbc p ↔ a ≤ p := by
  rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
  simp only [zagBlockSwap_val, zagBlockSwapNat]
  split_ifs <;> omega

theorem zagBlockSwap_symm_preserves_leftCut {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) :
    a ≤ (zagBlockSwap a b c hab hbc).symm p ↔ a ≤ p := by
  have h := zagBlockSwap_preserves_leftCut a b c
    ((zagBlockSwap a b c hab hbc).symm p) hab hbc
  simpa using h.symm

theorem zagBlockMiddle_le_unswap {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c)
    (hap : a < p) (hp : p ≤ b ∨ c ≤ p) :
    zagBlockMiddle a b c hab hbc ≤ (zagBlockSwap a b c hab hbc).symm p := by
  rw [Fin.le_iff_val_le_val]
  simp only [zagBlockMiddle_val, zagBlockSwap_symm_val,
    zagBlockUnswapNat]
  split_ifs <;> omega

theorem zagBlockSwap_right_of_middle_le {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c)
    (hqp : zagBlockMiddle a b c hab hbc < p)
    (hbp : b ≤ zagBlockSwap a b c hab hbc p) :
    c ≤ p := by
  rw [Fin.le_iff_val_le_val] at hbp ⊢
  rw [Fin.lt_def] at hqp
  simp only [zagBlockMiddle_val, zagBlockSwap_val, zagBlockSwapNat] at hbp hqp
  split_ifs at hbp <;> omega

theorem zagBlockSwap_symm_apply_of_right {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) (hcp : c < p) :
    (zagBlockSwap a b c hab hbc).symm p = p := by
  apply Fin.ext
  simp only [zagBlockSwap_symm_val, zagBlockUnswapNat]
  split_ifs <;> omega

theorem zagBlockSwapNat_reverse {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockSwapNat a (a + (c - b)) c p =
      zagBlockUnswapNat a b c p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

theorem zagBlockSwap_mul_reverse {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc *
        zagBlockSwap a (zagBlockMiddle a b c hab hbc) c
          (zagBlockMiddle_bounds a b c hab hbc).1
          (zagBlockMiddle_bounds a b c hab hbc).2 = 1 := by
  have hreverse :
      zagBlockSwap a (zagBlockMiddle a b c hab hbc) c
          (zagBlockMiddle_bounds a b c hab hbc).1
          (zagBlockMiddle_bounds a b c hab hbc).2 =
        (zagBlockSwap a b c hab hbc)⁻¹ := by
    ext p
    change zagBlockSwapNat a (a + (c - b)) c p =
      zagBlockUnswapNat a b c p
    exact zagBlockSwapNat_reverse
      (show (a : ℕ) < b by simpa using hab)
      (show (b : ℕ) < c by simpa using hbc)
  rw [hreverse, mul_inv_cancel]

@[simp]
theorem zagBlockSwap_inv_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    ((zagBlockSwap a b c hab hbc)⁻¹ p : ℕ) =
      zagBlockUnswapNat a b c p :=
  rfl

end MetaMathlibExt
