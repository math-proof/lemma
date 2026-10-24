import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.OrthogonalityLines
open Finset OrthogonalityLines


namespace OrthogonalityLines

/--
[affineLine_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma affineLine_card
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b c : ZMod p}
-- given
  (hab : (a, b) ≠ (0, 0)) :
-- imply
  (affineLine a b c).card = p := by
-- proof
  unfold affineLine
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by intro ha; exact hab (Prod.ext ha hb)
    subst hb; simp only [zero_mul, add_zero]
    have h_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a * xy.1 = c) =
      (Finset.univ : Finset (ZMod p)).image (fun y => (a⁻¹ * c, y)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h
        exact ⟨y, (mul_left_cancel₀ ha (by
          rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]; exact h.symm)), rfl⟩
      · rintro ⟨y', hx, hy⟩
        rw [← hx, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [h_eq, Finset.card_image_of_injective _ (fun y₁ y₂ h => by
      simp only [Prod.mk.injEq] at h; exact h.2), Finset.card_univ, ZMod.card]
  · have h_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a * xy.1 + b * xy.2 = c) =
    (Finset.univ : Finset (ZMod p)).image (fun x => (x, b⁻¹ * (c - a * x))) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨x, rfl, ?_⟩
      have key : b * y = c - a * x := by linear_combination h
      calc b⁻¹ * (c - a * x) = b⁻¹ * (b * y) := by rw [key]
        _ = y := inv_mul_cancel_left₀ hb y
    · rintro ⟨x', hx, hy⟩
      rw [← hx, ← hy]
      have : b * (b⁻¹ * (c - a * x')) = c - a * x' := mul_inv_cancel_left₀ hb _
      linear_combination this
    rw [h_eq, Finset.card_image_of_injective _ (fun x₁ x₂ h => by
      simp only [Prod.mk.injEq] at h; exact h.1), Finset.card_univ, ZMod.card]

end OrthogonalityLines

namespace OrthogonalityLines

/--
[IsAffineLine.card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma IsAffineLine.card_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L : Finset (ZMod p × ZMod p)}
-- given
  (hL : IsAffineLine L) :
-- imply
  L.card = p := by
-- proof
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  exact affineLine_card a b c hab

end OrthogonalityLines

namespace OrthogonalityLines

/--
[linear_system_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma linear_system_unique
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a₁ b₁ a₂ b₂ dx dy : ZMod p}
-- given
  (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
  (heq1 : a₁ * dx + b₁ * dy = 0)
  (heq2 : a₂ * dx + b₂ * dy = 0) :
-- imply
  dx = 0 ∧ dy = 0 := by
-- proof
  have hdx : (a₁ * b₂ - a₂ * b₁) * dx = 0 := by linear_combination b₂ * heq1 - b₁ * heq2
  have hdy : (a₁ * b₂ - a₂ * b₁) * dy = 0 := by linear_combination -(a₂ * heq1 - a₁ * heq2)
  exact ⟨(mul_eq_zero.mp hdx).resolve_left hdet, (mul_eq_zero.mp hdy).resolve_left hdet⟩

end OrthogonalityLines

namespace OrthogonalityLines

/--
[affineLine_mem_iff_of_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma affineLine_mem_iff_of_proportional
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a₁ b₁ c₁ a₂ b₂ c₂ : ZMod p}
  {x' y' : ZMod p}
-- given
  (hab₁ : (a₁, b₁) ≠ (0, 0))
  (hab₂ : (a₂, b₂) ≠ (0, 0))
  (hsub : a₁ * b₂ = a₂ * b₁)
  (hcross_b : c₁ * b₂ = c₂ * b₁)
  (hcross_a : c₁ * a₂ = c₂ * a₁) :
-- imply
  a₁ * x' + b₁ * y' = c₁ ↔ a₂ * x' + b₂ * y' = c₂ := by
-- proof
  constructor
  · intro h'
    by_cases ha₁ : a₁ = 0
    · have hb₁ : b₁ ≠ 0 := by intro hb₁; exact hab₁ (Prod.ext ha₁ hb₁)
      have ha₂ : a₂ = 0 := by
        have : a₂ * b₁ = 0 := by rw [← hsub, ha₁, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hb₁
      simp only [ha₁, ha₂, zero_mul, zero_add] at h' ⊢
      exact mul_left_cancel₀ hb₁ (by
        calc b₁ * (b₂ * y') = b₂ * (b₁ * y') := by ring
          _ = b₂ * c₁ := by rw [h']
          _ = c₁ * b₂ := by ring
          _ = c₂ * b₁ := hcross_b
          _ = b₁ * c₂ := by ring)
    · exact mul_left_cancel₀ ha₁ (by
      calc a₁ * (a₂ * x' + b₂ * y')
        = a₂ * (a₁ * x' + b₁ * y') + (a₁ * b₂ - a₂ * b₁) * y' := by ring
        _ = a₂ * c₁ + (a₁ * b₂ - a₂ * b₁) * y' := by rw [h']
        _ = a₂ * c₁ + 0 := by rw [sub_eq_zero.mpr hsub, zero_mul]
        _ = c₁ * a₂ := by ring
        _ = c₂ * a₁ := hcross_a
        _ = a₁ * c₂ := by ring)
  · intro h'
    by_cases ha₂ : a₂ = 0
    · have hb₂ : b₂ ≠ 0 := by intro hb₂; exact hab₂ (Prod.ext ha₂ hb₂)
      have ha₁' : a₁ = 0 := by
        have : a₁ * b₂ = 0 := by rw [hsub, ha₂, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hb₂
      simp only [ha₂, ha₁', zero_mul, zero_add] at h' ⊢
      exact mul_left_cancel₀ hb₂ (by
        calc b₂ * (b₁ * y') = b₁ * (b₂ * y') := by ring
          _ = b₁ * c₂ := by rw [h']
          _ = c₂ * b₁ := by ring
          _ = c₁ * b₂ := hcross_b.symm
          _ = b₂ * c₁ := by ring)
    · exact mul_left_cancel₀ ha₂ (by
      calc a₂ * (a₁ * x' + b₁ * y')
        = a₁ * (a₂ * x' + b₂ * y') + (a₂ * b₁ - a₁ * b₂) * y' := by ring
        _ = a₁ * c₂ + (a₂ * b₁ - a₁ * b₂) * y' := by rw [h']
        _ = a₁ * c₂ + 0 := by rw [sub_eq_zero.mpr hsub.symm, zero_mul]
        _ = c₂ * a₁ := by ring
        _ = c₁ * a₂ := hcross_a.symm
        _ = a₂ * c₁ := by ring)

end OrthogonalityLines

namespace OrthogonalityLines

/--
[affineLine_inter_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma affineLine_inter_card
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a₁ b₁ c₁ a₂ b₂ c₂ : ZMod p}
-- given
  (hab₁ : (a₁, b₁) ≠ (0, 0))
  (hab₂ : (a₂, b₂) ≠ (0, 0))
  (hdist : affineLine a₁ b₁ c₁ ≠ affineLine a₂ b₂ c₂) :
-- imply
  (affineLine a₁ b₁ c₁ ∩ affineLine a₂ b₂ c₂).card ≤ 1 := by
-- proof
  unfold affineLine at hdist ⊢
  have hinter_eq : Finset.univ.filter (fun xy : ZMod p × ZMod p => a₁ * xy.1 + b₁ * xy.2 = c₁) ∩
    Finset.univ.filter (fun xy => a₂ * xy.1 + b₂ * xy.2 = c₂) =
    Finset.univ.filter (fun xy => a₁ * xy.1 + b₁ * xy.2 = c₁ ∧ a₂ * xy.1 + b₂ * xy.2 = c₂) := by
    ext x; simp [Finset.mem_filter, Finset.mem_inter]
  rw [hinter_eq, Finset.card_le_one]
  intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  obtain ⟨h1a, h1b⟩ := h₁
  obtain ⟨h2a, h2b⟩ := h₂
  have heq1 : a₁ * (x₁ - x₂) + b₁ * (y₁ - y₂) = 0 := by linear_combination h1a - h2a
  have heq2 : a₂ * (x₁ - x₂) + b₂ * (y₁ - y₂) = 0 := by linear_combination h1b - h2b
  by_cases hdet : a₁ * b₂ - a₂ * b₁ ≠ 0
  ·
    obtain ⟨hdx, hdy⟩ := linear_system_unique a₁ b₁ a₂ b₂ _ _ hdet heq1 heq2
    exact Prod.ext (sub_eq_zero.mp hdx) (sub_eq_zero.mp hdy)
  ·
    simp only [not_not] at hdet
    exfalso; apply hdist
    have hsub : a₁ * b₂ = a₂ * b₁ := sub_eq_zero.mp hdet
    have hcross_b : c₁ * b₂ = c₂ * b₁ := by
      calc c₁ * b₂ = (a₁ * x₁ + b₁ * y₁) * b₂ := by rw [h1a]
        _ = a₁ * b₂ * x₁ + b₁ * b₂ * y₁ := by ring
        _ = a₂ * b₁ * x₁ + b₂ * b₁ * y₁ := by rw [hsub, mul_comm b₁ b₂]
        _ = (a₂ * x₁ + b₂ * y₁) * b₁ := by ring
        _ = c₂ * b₁ := by rw [h1b]
    have hcross_a : c₁ * a₂ = c₂ * a₁ := by
      calc c₁ * a₂ = (a₁ * x₁ + b₁ * y₁) * a₂ := by rw [h1a]
        _ = a₁ * a₂ * x₁ + b₁ * a₂ * y₁ := by ring
        _ = a₁ * a₂ * x₁ + a₁ * b₂ * y₁ := by
          congr 1
          calc b₁ * a₂ * y₁ = a₂ * b₁ * y₁ := by ring
            _ = a₁ * b₂ * y₁ := by rw [hsub.symm]
        _ = a₁ * (a₂ * x₁ + b₂ * y₁) := by ring
        _ = a₁ * c₂ := by rw [h1b]
        _ = c₂ * a₁ := by ring
    ext ⟨x', y'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact affineLine_mem_iff_of_proportional a₁ b₁ c₁ a₂ b₂ c₂ hab₁ hab₂ hsub hcross_b hcross_a x' y'

end OrthogonalityLines

namespace OrthogonalityLines

/--
[IsAffineLine.inter_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma IsAffineLine.inter_card_le_one
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L₁ L₂ : Finset (ZMod p × ZMod p)}
-- given
  (hL₁ : IsAffineLine L₁)
  (hL₂ : IsAffineLine L₂)
  (hdist : L₁ ≠ L₂) :
-- imply
  (L₁ ∩ L₂).card ≤ 1 := by
-- proof
  obtain ⟨a₁, b₁, c₁, hab₁, rfl⟩ := hL₁
  obtain ⟨a₂, b₂, c₂, hab₂, rfl⟩ := hL₂
  exact affineLine_inter_card a₁ b₁ c₁ a₂ b₂ c₂ hab₁ hab₂ hdist

end OrthogonalityLines

namespace OrthogonalityLines

/--
[innerProduct_highFreq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma innerProduct_highFreq_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L₁ L₂ : Finset (ZMod p × ZMod p)}
-- given
  (hL₁ : L₁.card = p)
  (hL₂ : L₂.card = p) :
-- imply
  ∑ x : ZMod p × ZMod p, lineHighFreq L₁ x * lineHighFreq L₂ x = ((L₁ ∩ L₂).card : ℝ) - 1 := by
-- proof
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
  unfold lineHighFreq
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
    push_cast
    field_simp
  rw [hS1, hS2, hS3, hS4]
  ring

end OrthogonalityLines

namespace OrthogonalityLines

/--
[orthogonality_lines](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityLines.lean)
-/
@[path]
lemma orthogonality_lines
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {L₁ L₂ : Finset (ZMod p × ZMod p)}
-- given
  (hL₁ : IsAffineLine L₁)
  (hL₂ : IsAffineLine L₂)
  (hdist : L₁ ≠ L₂) :
-- imply
  ∑ x : ZMod p × ZMod p, lineHighFreq L₁ x * lineHighFreq L₂ x ≤ 0 := by
-- proof
  rw [innerProduct_highFreq_eq L₁ L₂ hL₁.card_eq hL₂.card_eq]
  have hinter := hL₁.inter_card_le_one hL₂ hdist
  have hcard : ((L₁ ∩ L₂).card : ℝ) ≤ 1 := by exact_mod_cast hinter
  linarith

end OrthogonalityLines


-- created on 2026-10-23
