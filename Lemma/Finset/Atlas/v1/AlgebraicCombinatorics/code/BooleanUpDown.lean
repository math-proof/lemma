import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
open Finset BigOperators BooleanUpDown


namespace BooleanUpDown

/--
[innerProd_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma innerProd_comm
  {n : ℕ}
  [Fintype α]
  {f g : α → ℝ} :
-- imply
  innerProd f g = innerProd g f := by
-- proof
  simp only [innerProd]; congr 1; ext x; ring

end BooleanUpDown

namespace BooleanUpDown

/--
[adjointness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma adjointness
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ}
  {w : Level n (i + 1) → ℝ} :
-- imply
  innerProd (up i v) w = innerProd v (down i w) := by
-- proof
  simp only [innerProd, up, down]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext x; congr 1; ext y; split_ifs <;> ring

end BooleanUpDown

namespace BooleanUpDown

/--
[level_filter_card_eq_DU](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma level_filter_card_eq_DU
  {n : ℕ}
  {i : ℕ}
  {x z : Level n i} :
-- imply
  (Finset.univ.filter (fun y : Level n (i + 1) => x.val ⊆ y.val ∧ z.val ⊆ y.val)).card = BooleanCommutator.DU_coeff i x.val z.val := by
-- proof
  simp only [BooleanCommutator.DU_coeff]
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy; simp only [mem_filter, mem_univ, true_and] at hy ⊢; exact ⟨y.property, hy.1, hy.2⟩
  · intro y1 _ y2 _ h; exact Subtype.val_injective h
  · intro s hs; simp only [mem_filter, mem_univ, true_and] at hs
    exact ⟨⟨s, hs.1⟩, by simp [mem_filter, hs.2.1, hs.2.2], rfl⟩

end BooleanUpDown

namespace BooleanUpDown

/--
[down_up_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma down_up_apply
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ}
  {x : Level n i} :
-- imply
  down i (up i v) x = ∑ z : Level n i, (BooleanCommutator.DU_coeff i x.val z.val : ℝ) * v z := by
-- proof
  simp only [down, up]
  conv_lhs =>
    arg 2; ext y
    rw [show (if x.val ⊆ y.val then
      ∑ z : Level n i, if z.val ⊆ y.val then v z else 0 else 0) =
      ∑ z : Level n i, if (x.val ⊆ y.val ∧ z.val ⊆ y.val) then v z else 0
      from by split_ifs with h <;> simp [h]]
  rw [Finset.sum_comm]
  congr 1; ext z
  simp only [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, level_filter_card_eq_DU]

end BooleanUpDown

namespace BooleanUpDown

/--
[level_filter_card_eq_UD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma level_filter_card_eq_UD
  {n : ℕ}
  {k : ℕ}
  {x z : Level n (k + 1)} :
-- imply
  (Finset.univ.filter (fun w : Level n k => w.val ⊆ x.val ∧ w.val ⊆ z.val)).card = BooleanCommutator.UD_coeff (k + 1) x.val z.val := by
-- proof
  simp only [BooleanCommutator.UD_coeff]
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw; simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact ⟨w.property, hw.1, hw.2⟩
  · intro w1 _ w2 _ h; exact Subtype.val_injective h
  · intro s hs; simp only [mem_filter, mem_univ, true_and] at hs
    exact ⟨⟨s, hs.1⟩, by simp [mem_filter, hs.2.1, hs.2.2], rfl⟩

end BooleanUpDown

namespace BooleanUpDown

/--
[up_down_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma up_down_apply
  {n : ℕ}
  {k : ℕ}
  {v : Level n (k + 1) → ℝ}
  {x : Level n (k + 1)} :
-- imply
  up k (down k v) x = ∑ z : Level n (k + 1), (BooleanCommutator.UD_coeff (k + 1) x.val z.val : ℝ) * v z := by
-- proof
  simp only [up, down]
  conv_lhs =>
    arg 2; ext w
    rw [show (if w.val ⊆ x.val then
      ∑ y : Level n (k + 1), if w.val ⊆ y.val then v y else 0 else 0) =
      ∑ z : Level n (k + 1), if (w.val ⊆ x.val ∧ w.val ⊆ z.val) then v z else 0
      from by split_ifs with h <;> simp [h]]
  rw [Finset.sum_comm]
  congr 1; ext z
  simp only [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1; exact_mod_cast level_filter_card_eq_UD k x z

end BooleanUpDown

namespace BooleanUpDown

/--
[DU_form_eq_inner_up](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma DU_form_eq_inner_up
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ} :
-- imply
  DU_form i v v = innerProd (up i v) (up i v) := by
-- proof
  have h1 : DU_form i v v = innerProd (down i (up i v)) v := by
    simp only [DU_form, innerProd, down_up_apply, Finset.sum_mul]
    congr 1; ext x; congr 1; ext z; ring
  rw [h1, innerProd_comm]
  exact (adjointness i v (up i v)).symm

end BooleanUpDown

namespace BooleanUpDown

/--
[UD_form_succ_eq_inner_down](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma UD_form_succ_eq_inner_down
  {n : ℕ}
  {k : ℕ}
  {v : Level n (k + 1) → ℝ} :
-- imply
  UD_form (k + 1) v v = innerProd (down k v) (down k v) := by
-- proof
  have h1 : UD_form (k + 1) v v = innerProd (up k (down k v)) v := by
    simp only [UD_form, innerProd, up_down_apply, Finset.sum_mul]
    congr 1; ext x; congr 1; ext z; ring
  rw [h1]
  exact adjointness k (down k v) v

end BooleanUpDown

namespace BooleanUpDown

/--
[UD_form_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma UD_form_nonneg
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ} :
-- imply
  0 ≤ UD_form i v v := by
-- proof
  cases i with
  | zero =>
    simp only [UD_form, BooleanCommutator.UD_coeff, Nat.cast_zero, zero_mul,
      Finset.sum_const_zero]; exact le_refl _
  | succ k =>
    rw [UD_form_succ_eq_inner_down]
    exact Finset.sum_nonneg fun w _ => mul_self_nonneg (down k v w)

end BooleanUpDown

namespace BooleanUpDown

/--
[DU_minus_UD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma DU_minus_UD
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ}
-- given
  (hi : i ≤ n) :
-- imply
  DU_form i v v - UD_form i v v = ((n : ℝ) - 2 * i) * ∑ x : Level n i, v x * v x := by
-- proof
  simp only [DU_form, UD_form, ← Finset.sum_sub_distrib]
  have key : ∀ (x z : Level n i),
    (BooleanCommutator.DU_coeff i x.val z.val : ℝ) * v x * v z -
    (BooleanCommutator.UD_coeff i x.val z.val : ℝ) * v x * v z =
    (if z = x then ((n : ℝ) - 2 * i) else 0) * v x * v z := by
    intro x z
    by_cases hzx : z = x
    · subst hzx; simp only [if_true]
      rw [BooleanCommutator.DU_coeff_diag i z.val z.property,
        BooleanCommutator.UD_coeff_diag i z.val z.property]
      push_cast [Nat.cast_sub hi]; ring
    · simp only [hzx, if_false, zero_mul, sub_eq_zero]
      have hne : x.val ≠ z.val := fun h => hzx (Subtype.val_injective h.symm)
      rw [BooleanCommutator.DU_UD_coeff_off_diag i x.val z.val x.property z.property hne]
  simp_rw [key, Finset.mul_sum]
  congr 1; ext x
  have : ∀ z : Level n i, (if z = x then ((n : ℝ) - 2 * ↑i) else 0) * v x * v z =
    if z = x then ((n : ℝ) - 2 * ↑i) * v x * v z else 0 := by
    intro z; split_ifs <;> ring
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring

end BooleanUpDown

namespace BooleanUpDown

/--
[up_ker_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma up_ker_trivial
  {n : ℕ}
  {i : ℕ}
  {v : Level n i → ℝ}
-- given
  (hi : 2 * i < n)
  (hv : up (n := n) i v = 0) :
-- imply
  v = 0 := by
-- proof
  have hDU : DU_form i v v = 0 := by
    rw [DU_form_eq_inner_up]
    simp only [innerProd, hv, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hUD_nn : 0 ≤ UD_form i v v := UD_form_nonneg i v
  have hcomm := DU_minus_UD i v (by omega : i ≤ n)
  have hn2i : (0 : ℝ) < (n : ℝ) - 2 * (i : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < (n : ℤ) - 2 * (i : ℤ) from by omega)
  have hvsq_le : ∑ x : Level n i, v x * v x ≤ 0 := by nlinarith
  have hvsq_ge : 0 ≤ ∑ x : Level n i, v x * v x :=
    Finset.sum_nonneg fun x _ => mul_self_nonneg (v x)
  have hvsq : ∑ x : Level n i, v x * v x = 0 := le_antisymm hvsq_le hvsq_ge
  ext x
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => mul_self_nonneg (v x))).mp hvsq x (Finset.mem_univ x)
  exact mul_self_eq_zero.mp this

end BooleanUpDown

namespace BooleanUpDown

/--
[up_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean)
-/
@[path]
lemma up_injective
  {n : ℕ}
  {i : ℕ}
-- given
  (hi : 2 * i < n) :
-- imply
  Function.Injective (up (n := n) i) := by
-- proof
  intro a b hab
  have hsub : up i (a - b) = 0 := by
    ext y; simp only [up, Pi.sub_apply, Pi.zero_apply]
    have := congr_fun hab y; simp only [up] at this
    rw [show (∑ x : Level n i, if x.val ⊆ y.val then (a x - b x) else 0) =
      (∑ x, if x.val ⊆ y.val then a x else 0) -
      (∑ x, if x.val ⊆ y.val then b x else 0)
      from by rw [← Finset.sum_sub_distrib]; congr 1; ext x; split_ifs <;> ring]
    linarith
  have hzero := up_ker_trivial i hi (a - b) hsub
  ext x
  have := congr_fun hzero x
  simp [Pi.sub_apply] at this
  linarith

end BooleanUpDown


-- created on 2026-10-23
