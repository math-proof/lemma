import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemmaFF
open Finset MainLemmaFF


namespace MainLemmaFF

/--
[decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma decomposition
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
  {x : F × F} :
-- imply
  lineSumFunc ℒ x = constPart ℒ x + highFreqPart ℒ x := by
-- proof
  simp only [lineSumFunc, constPart, highFreqPart, lineHighFreq, lineIndicator]
  rw [Finset.sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  ring

end MainLemmaFF

namespace MainLemmaFF

/--
[l2_norm_constPart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma l2_norm_constPart
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))} :
-- imply
  ∑ x : F × F, (constPart ℒ x) ^ 2 = (ℒ.card : ℝ) ^ 2 := by
-- proof
  simp only [constPart]
  rw [sum_const, card_univ, Fintype.card_prod]
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [nsmul_eq_mul]
  field_simp
  push_cast
  ring

end MainLemmaFF

namespace MainLemmaFF

/--
[innerProduct_lineHighFreq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma innerProduct_lineHighFreq_eq
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {L₁ L₂ : Finset (F × F)}
-- given
  (hL₁ : L₁.card = Fintype.card F)
  (hL₂ : L₂.card = Fintype.card F) :
-- imply
  ∑ x : F × F, lineHighFreq L₁ x * lineHighFreq L₂ x = ((L₁ ∩ L₂).card : ℝ) - 1 := by
-- proof
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [lineHighFreq]
  have hexpand : ∀ x : F × F,
    ((if x ∈ L₁ then (1 : ℝ) else 0) - (Fintype.card F : ℝ)⁻¹) *
    ((if x ∈ L₂ then (1 : ℝ) else 0) - (Fintype.card F : ℝ)⁻¹) =
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0)
    - (Fintype.card F : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0)
    - (Fintype.card F : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0)
    + (Fintype.card F : ℝ)⁻¹ ^ 2 := by intro x; ring
  simp_rw [hexpand, sum_add_distrib, sum_sub_distrib]
  have hS1 : ∑ x : F × F,
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
    ((L₁ ∩ L₂).card : ℝ) := by
    have h1 : ∀ x, (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
      if (x ∈ L₁ ∧ x ∈ L₂) then 1 else 0 := by intro x; split_ifs <;> simp_all
    simp_rw [h1, show (fun x => if x ∈ L₁ ∧ x ∈ L₂ then (1 : ℝ) else 0) =
      fun x => if x ∈ L₁ ∩ L₂ then 1 else 0 from by ext x; simp [mem_inter]]
    rw [sum_boole]
    exact_mod_cast show (univ.filter (· ∈ L₁ ∩ L₂)).card = (L₁ ∩ L₂).card from by
      congr 1; ext x; simp
  have hS2 : ∑ x : F × F,
    (Fintype.card F : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₁)).card : ℝ) = (Fintype.card F : ℝ) from by
      have : (univ.filter (· ∈ L₁)).card = L₁.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₁)]
    exact inv_mul_cancel₀ hq
  have hS3 : ∑ x : F × F,
    (Fintype.card F : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₂)).card : ℝ) = (Fintype.card F : ℝ) from by
      have : (univ.filter (· ∈ L₂)).card = L₂.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₂)]
    exact inv_mul_cancel₀ hq
  have hS4 : ∑ x : F × F, (Fintype.card F : ℝ)⁻¹ ^ 2 = 1 := by
    rw [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, inv_pow]
    push_cast; field_simp
  rw [hS1, hS2, hS3, hS4]; ring

end MainLemmaFF

namespace MainLemmaFF

/--
[l2_bound_highFreqPart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma l2_bound_highFreqPart
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
-- given
  (hsize : ∀ L ∈ ℒ, L.card = Fintype.card F)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card = 1) :
-- imply
  ∑ x : F × F, (highFreqPart ℒ x) ^ 2 = (ℒ.card : ℝ) * ((Fintype.card F : ℝ) - 1) := by
-- proof
  simp only [highFreqPart]
  have hexpand : ∀ x : F × F,
    (∑ L ∈ ℒ, lineHighFreq L x) ^ 2 =
    ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, lineHighFreq L₁ x * lineHighFreq L₂ x := by
    intro x; rw [sq, Finset.sum_mul]; congr 1; ext L₁; rw [mul_sum]
  simp_rw [hexpand]
  rw [sum_comm]; simp_rw [sum_comm (s := univ)]
  have hcross : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ →
    ∑ x : F × F, lineHighFreq L₁ x * lineHighFreq L₂ x = 0 := by
    intro L₁ hL₁ L₂ hL₂ hne
    rw [innerProduct_lineHighFreq_eq L₁ L₂ (hsize L₁ hL₁) (hsize L₂ hL₂)]
    have h := hinter L₁ hL₁ L₂ hL₂ hne
    simp [h]
  have hdiag : ∀ L₁ ∈ ℒ,
    ∑ x : F × F, lineHighFreq L₁ x * lineHighFreq L₁ x =
    (Fintype.card F : ℝ) - 1 := by
    intro L₁ hL₁
    have key := innerProduct_lineHighFreq_eq L₁ L₁ (hsize L₁ hL₁) (hsize L₁ hL₁)
    simp only [inter_self, hsize L₁ hL₁] at key
    linarith
  have hsimpl : ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, ∑ x : F × F,
    lineHighFreq L₁ x * lineHighFreq L₂ x =
    ∑ L₁ ∈ ℒ, ((Fintype.card F : ℝ) - 1) := by
    apply sum_congr rfl
    intro L₁ hL₁
    have hsplit : ∑ L₂ ∈ ℒ, ∑ x, lineHighFreq L₁ x * lineHighFreq L₂ x =
      ∑ x, lineHighFreq L₁ x * lineHighFreq L₁ x +
      ∑ L₂ ∈ ℒ.erase L₁, ∑ x, lineHighFreq L₁ x * lineHighFreq L₂ x := by
      rw [← Finset.add_sum_erase ℒ _ hL₁]
    rw [hsplit]
    have hoff : ∑ L₂ ∈ ℒ.erase L₁, ∑ x, lineHighFreq L₁ x * lineHighFreq L₂ x = 0 := by
      apply Finset.sum_eq_zero
      intro L₂ hL₂
      exact hcross L₁ hL₁ L₂ (mem_of_mem_erase hL₂) (ne_of_mem_erase hL₂).symm
    rw [hoff, add_zero]
    exact hdiag L₁ hL₁
  rw [hsimpl, sum_const, nsmul_eq_mul]

end MainLemmaFF

namespace MainLemmaFF

/--
[l2_bound_highFreqPart_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma l2_bound_highFreqPart_le
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
-- given
  (hsize : ∀ L ∈ ℒ, L.card = Fintype.card F)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card = 1) :
-- imply
  ∑ x : F × F, (highFreqPart ℒ x) ^ 2 ≤ (ℒ.card : ℝ) * (Fintype.card F : ℝ) := by
-- proof
  rw [l2_bound_highFreqPart ℒ hsize hinter]
  have hcard : (0 : ℝ) ≤ (ℒ.card : ℝ) := Nat.cast_nonneg _
  linarith [mul_le_mul_of_nonneg_left (sub_le_self (Fintype.card F : ℝ) one_pos.le) hcard]

end MainLemmaFF

namespace MainLemmaFF

/--
[constPart_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma constPart_const
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
  {x y : F × F} :
-- imply
  constPart ℒ x = constPart ℒ y :=
-- proof
  rfl

end MainLemmaFF

namespace MainLemmaFF

/--
[sum_highFreqPart_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma sum_highFreqPart_eq_zero
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
-- given
  (hsize : ∀ L ∈ ℒ, L.card = Fintype.card F) :
-- imply
  ∑ x : F × F, highFreqPart ℒ x = 0 := by
-- proof
  simp only [highFreqPart]
  rw [sum_comm]
  apply Finset.sum_eq_zero
  intro L hL
  simp only [lineHighFreq]
  rw [sum_sub_distrib, sum_boole, sum_const]
  have hfilt : (univ.filter (· ∈ L)).card = L.card := by
    congr 1; ext x; simp
  rw [hfilt, hsize L hL]
  rw [card_univ, Fintype.card_prod, nsmul_eq_mul]
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  push_cast
  ring

end MainLemmaFF

namespace MainLemmaFF

/--
[main_lemma_ff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaFF.lean)
-/
@[path]
lemma main_lemma_ff
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {ℒ : Finset (Finset (F × F))}
-- given
  (hsize : ∀ L ∈ ℒ, L.card = Fintype.card F)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card = 1) :
-- imply
  (∀ x, lineSumFunc ℒ x = constPart ℒ x + highFreqPart ℒ x) ∧ (∀ x y : F × F, constPart ℒ x = constPart ℒ y) ∧ (∑ x : F × F, highFreqPart ℒ x = 0) ∧ (∑ x : F × F, (constPart ℒ x) ^ 2 = (ℒ.card : ℝ) ^ 2) ∧ (∑ x : F × F, (highFreqPart ℒ x) ^ 2 = (ℒ.card : ℝ) * ((Fintype.card F : ℝ) - 1)) ∧ (∑ x : F × F, (highFreqPart ℒ x) ^ 2 ≤ (ℒ.card : ℝ) * (Fintype.card F : ℝ)) :=
-- proof
  ⟨decomposition ℒ, constPart_const ℒ, sum_highFreqPart_eq_zero ℒ hsize,
    l2_norm_constPart ℒ, l2_bound_highFreqPart ℒ hsize hinter,
    l2_bound_highFreqPart_le ℒ hsize hinter⟩

end MainLemmaFF


-- created on 2026-10-23
