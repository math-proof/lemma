import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemma2F
open Finset LineSumDecomposition


namespace LineSumDecomposition

/--
[decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma decomposition
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
  {x : ZMod p × ZMod p} :
-- imply
  lineSumFn ℒ x = lineSumConst ℒ + lineSumHighFreq ℒ x := by
-- proof
  simp [lineSumHighFreq]

end LineSumDecomposition

namespace LineSumDecomposition

/--
[lineSumHighFreq_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma lineSumHighFreq_eq_sum
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
  {x : ZMod p × ZMod p} :
-- imply
  lineSumHighFreq ℒ x = ∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
-- proof
  simp only [lineSumHighFreq, lineSumFn, lineSumConst, div_eq_mul_inv,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

end LineSumDecomposition

namespace LineSumDecomposition

/--
[sum_lineSumFn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma sum_lineSumFn
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
-- given
  (hlines : ∀ L ∈ ℒ, L.card = p) :
-- imply
  ∑ x : ZMod p × ZMod p, lineSumFn ℒ x = (ℒ.card : ℝ) * (p : ℝ) := by
-- proof
  unfold lineSumFn
  rw [Finset.sum_comm]
  have h : ∀ L ∈ ℒ, ∑ x : ZMod p × ZMod p, (if x ∈ L then (1 : ℝ) else 0) = (p : ℝ) := by
    intro L hL
    rw [sum_boole]
    rw [show ((Finset.univ.filter (· ∈ L)).card : ℝ) = (p : ℝ) from by
      have hfilt : (Finset.univ.filter (· ∈ L)).card = L.card := by
        congr 1; ext x; simp
      exact_mod_cast (hfilt ▸ hlines L hL)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

end LineSumDecomposition

namespace LineSumDecomposition

/--
[orthogonal_const_highFreq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma orthogonal_const_highFreq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
-- given
  (hlines : ∀ L ∈ ℒ, L.card = p) :
-- imply
  ∑ x : ZMod p × ZMod p, lineSumConst ℒ * lineSumHighFreq ℒ x = 0 := by
-- proof
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  simp only [lineSumHighFreq]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hsum : ∑ x : ZMod p × ZMod p, lineSumFn ℒ x = (ℒ.card : ℝ) * (p : ℝ) :=
    sum_lineSumFn ℒ hlines
  have hconst : ∑ x : ZMod p × ZMod p, lineSumConst ℒ =
    (ℒ.card : ℝ) * (p : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
      nsmul_eq_mul, lineSumConst]
    field_simp
    push_cast; ring
  rw [hsum, hconst, sub_self, mul_zero]

end LineSumDecomposition

namespace LineSumDecomposition

/--
[norm_sq_const_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma norm_sq_const_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))} :
-- imply
  ∑ _x : ZMod p × ZMod p, (lineSumConst ℒ) ^ 2 = (ℒ.card : ℝ) ^ 2 := by
-- proof
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
    nsmul_eq_mul, lineSumConst]
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  field_simp
  push_cast; ring

end LineSumDecomposition

namespace LineSumDecomposition

/--
[cross_term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma cross_term_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L₁ L₂ : Finset (ZMod p × ZMod p)}
-- given
  (hL₁ : L₁.card = p)
  (hL₂ : L₂.card = p) :
-- imply
  ∑ x : ZMod p × ZMod p, ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) * ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) = ((L₁ ∩ L₂).card : ℝ) - 1 := by
-- proof
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  have hexpand : ∀ x : ZMod p × ZMod p,
    ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
    ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) =
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0)
    - (p : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0)
    - (p : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0)
    + (p : ℝ)⁻¹ ^ 2 := by intro x; ring
  simp_rw [hexpand]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib]
  have hS1 : ∑ x : ZMod p × ZMod p,
    (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
    ((L₁ ∩ L₂).card : ℝ) := by
    have h1 : ∀ x, (if x ∈ L₁ then (1 : ℝ) else 0) * (if x ∈ L₂ then (1 : ℝ) else 0) =
      if (x ∈ L₁ ∧ x ∈ L₂) then 1 else 0 := by intro x; split_ifs <;> simp_all
    simp_rw [h1, show (fun x => if x ∈ L₁ ∧ x ∈ L₂ then (1:ℝ) else 0) =
      fun x => if x ∈ L₁ ∩ L₂ then 1 else 0 from by ext x; simp [mem_inter]]
    rw [sum_boole]
    exact_mod_cast show (univ.filter (· ∈ L₁ ∩ L₂)).card = (L₁ ∩ L₂).card from by
      congr 1; ext x; simp
  have hS2 : ∑ x : ZMod p × ZMod p,
    (p : ℝ)⁻¹ * (if x ∈ L₁ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₁)).card : ℝ) = (p : ℝ) from by
      have : (univ.filter (· ∈ L₁)).card = L₁.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₁)]
    exact inv_mul_cancel₀ hp
  have hS3 : ∑ x : ZMod p × ZMod p,
    (p : ℝ)⁻¹ * (if x ∈ L₂ then (1 : ℝ) else 0) = 1 := by
    rw [← mul_sum, sum_boole]
    rw [show ((univ.filter (· ∈ L₂)).card : ℝ) = (p : ℝ) from by
      have : (univ.filter (· ∈ L₂)).card = L₂.card := by congr 1; ext x; simp
      exact_mod_cast (this ▸ hL₂)]
    exact inv_mul_cancel₀ hp
  have hS4 : ∑ x : ZMod p × ZMod p, (p : ℝ)⁻¹ ^ 2 = 1 := by
    rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul, inv_pow]
    push_cast; field_simp
  rw [hS1, hS2, hS3, hS4]; ring

end LineSumDecomposition

namespace LineSumDecomposition

/--
[cross_term_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma cross_term_nonpos
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L₁ L₂ : Finset (ZMod p × ZMod p)}
-- given
  (hL₁ : L₁.card = p)
  (hL₂ : L₂.card = p)
  (_hne : L₁ ≠ L₂)
  (hinter : (L₁ ∩ L₂).card ≤ 1) :
-- imply
  ∑ x : ZMod p × ZMod p, ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) * ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ 0 := by
-- proof
  rw [cross_term_eq L₁ L₂ hL₁ hL₂]
  have hcard : ((L₁ ∩ L₂).card : ℝ) ≤ 1 := by exact_mod_cast hinter
  linarith

end LineSumDecomposition

namespace LineSumDecomposition

/--
[norm_sq_highFreq_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma norm_sq_highFreq_le
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
-- given
  (hlines : ∀ L ∈ ℒ, L.card = p)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
-- imply
  ∑ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 ≤ (ℒ.card : ℝ) * (p : ℝ) := by
-- proof
  have hrw : ∀ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 =
    (∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) ^ 2 := by
    intro x; rw [lineSumHighFreq_eq_sum]
  simp_rw [hrw]
  have hexpand : ∑ x : ZMod p × ZMod p,
    (∑ L ∈ ℒ, ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) ^ 2 =
    ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_comm (s := ℒ) (t := univ)]
  rw [hexpand]
  have step1 : ∑ L₁ ∈ ℒ, ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
    ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
    ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤
    ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro L₁ hL₁
    have hsplit : ∑ L₂ ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) =
      (∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹)) +
      ∑ L₂ ∈ ℒ.erase L₁, ∑ x : ZMod p × ZMod p,
        ((if x ∈ L₁ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L₂ then (1 : ℝ) else 0) - (p : ℝ)⁻¹) := by
      rw [← Finset.add_sum_erase _ _ hL₁]
    rw [hsplit]
    linarith [Finset.sum_nonpos (fun L₂ (hL₂ : L₂ ∈ ℒ.erase L₁) =>
      cross_term_nonpos L₁ L₂ (hlines L₁ hL₁) (hlines L₂ (Finset.mem_of_mem_erase hL₂))
        (Finset.ne_of_mem_erase hL₂).symm
        (hinter L₁ hL₁ L₂ (Finset.mem_of_mem_erase hL₂) (Finset.ne_of_mem_erase hL₂).symm))]
  have step2 : ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
    ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
    ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ (ℒ.card : ℝ) * (p : ℝ) := by
    have hdiag : ∀ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) ≤ (p : ℝ) := by
      intro L hL
      have heq : ∑ x : ZMod p × ZMod p,
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
        ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) = (p : ℝ) - 1 := by
        rw [cross_term_eq L L (hlines L hL) (hlines L hL)]
        simp [Finset.inter_self, hlines L hL]
      rw [heq]
      linarith [show (1 : ℝ) ≤ (p : ℝ) from by
        exact_mod_cast Nat.Prime.one_le (Fact.out)]
    calc ∑ L ∈ ℒ, ∑ x : ZMod p × ZMod p,
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹) *
      ((if x ∈ L then (1 : ℝ) else 0) - (p : ℝ)⁻¹)
      ≤ ∑ L ∈ ℒ, (p : ℝ) := Finset.sum_le_sum hdiag
      _ = (ℒ.card : ℝ) * (p : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end LineSumDecomposition

namespace LineSumDecomposition

/--
[main_lemma_2F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2F.lean)
-/
@[path]
lemma main_lemma_2F
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
-- given
  (hlines : ∀ L ∈ ℒ, L.card = p)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
-- imply
  (∀ x : ZMod p × ZMod p, lineSumFn ℒ x = lineSumConst ℒ + lineSumHighFreq ℒ x) ∧ (∑ x : ZMod p × ZMod p, lineSumConst ℒ * lineSumHighFreq ℒ x = 0) ∧ (∑ _x : ZMod p × ZMod p, (lineSumConst ℒ) ^ 2 = (ℒ.card : ℝ) ^ 2) ∧ (∑ x : ZMod p × ZMod p, (lineSumHighFreq ℒ x) ^ 2 ≤ (ℒ.card : ℝ) * (p : ℝ)) :=
-- proof
  ⟨decomposition ℒ, orthogonal_const_highFreq ℒ hlines, norm_sq_const_eq ℒ,
    norm_sq_highFreq_le ℒ hlines hinter⟩

end LineSumDecomposition


-- created on 2026-10-23
