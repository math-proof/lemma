import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.GSW
open Classical ProjectionTheory


namespace ProjectionTheory

/--
[gsw_two_ends_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/GSW.lean)
-/
@[path]
lemma gsw_two_ends_bound
-- imply
  ∃ (C₁ : ℝ), C₁ > 0 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))), 0 < E.card → (∀ x ∈ E, ‖x‖ ≤ 1) → (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) → ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) → ∀ (Rtilde : ℝ), δ ≤ Rtilde → Rtilde ≤ 1 → ∀ (𝒯_sub : Finset DeltaTube), (∀ T ∈ 𝒯_sub, T.width = δ) → (∀ T ∈ 𝒯_sub, (T.richness E : ℝ) ≥ R) → (∃ (E_sub : Finset (EuclideanSpace ℝ (Fin 2))), E_sub ⊆ E ∧ (E_sub.card : ℝ) ≤ Rtilde ∧ (∃ (witnesses : DeltaTube → Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), (∀ T ∈ 𝒯_sub, witnesses T ⊆ E_sub ×ˢ E_sub) ∧ (∀ T ∈ 𝒯_sub, (witnesses T).card ≥ ⌈R ^ 2 / 4⌉₊) ∧ (∀ T₁ ∈ 𝒯_sub, ∀ T₂ ∈ 𝒯_sub, T₁ ≠ T₂ → Disjoint (witnesses T₁) (witnesses T₂)))) → (𝒯_sub.card : ℝ) ≤ C₁ * Rtilde ^ 2 / R ^ 2 := by
-- proof
  refine ⟨4, by norm_num, ?_⟩
  intro δ _hδ _hδ1 E _hE_pos _hE_ball _hE_sep R hR _hR_le_N Rtilde _hδ_Rtilde _hRtilde1
    𝒯_sub _h𝒯_width _h𝒯_rich hcomb
  obtain ⟨E_sub, _hE_sub_ss, hE_sub_card, witnesses, hwit_ss, hwit_card, hwit_disj⟩ := hcomb
  have h_union_le : (𝒯_sub.biUnion witnesses).card ≤ (E_sub ×ˢ E_sub).card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨T, hT_mem, hp_wit⟩ := hp
    exact hwit_ss T hT_mem hp_wit
  have h_sum_eq : (𝒯_sub.biUnion witnesses).card = ∑ T ∈ 𝒯_sub, (witnesses T).card := by
    apply Finset.card_biUnion
    intro T₁ hT₁ T₂ hT₂ hne
    exact hwit_disj T₁ hT₁ T₂ hT₂ hne
  have h_sum_ge : 𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ ≤ ∑ T ∈ 𝒯_sub, (witnesses T).card := by
    have := Finset.card_nsmul_le_sum 𝒯_sub (fun T => (witnesses T).card) ⌈R ^ 2 / 4⌉₊ hwit_card
    omega
  have h_prod_card : (E_sub ×ˢ E_sub).card = E_sub.card ^ 2 := by
    rw [Finset.card_product, sq]
  have h_key : 𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ ≤ E_sub.card ^ 2 := by
    linarith [h_sum_ge, h_sum_eq ▸ h_union_le, h_prod_card ▸ (h_sum_eq ▸ h_union_le)]
  have hR2_pos : R ^ 2 > 0 := by positivity
  have h_ceil_ge : (⌈R ^ 2 / 4⌉₊ : ℝ) ≥ R ^ 2 / 4 := Nat.le_ceil _
  have h_key_real : (𝒯_sub.card : ℝ) * (R ^ 2 / 4) ≤ (E_sub.card : ℝ) ^ 2 := by
    calc (𝒯_sub.card : ℝ) * (R ^ 2 / 4)
      ≤ (𝒯_sub.card : ℝ) * (⌈R ^ 2 / 4⌉₊ : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_ceil_ge (Nat.cast_nonneg _)
      _ = ((𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((E_sub.card ^ 2 : ℕ) : ℝ) := by exact_mod_cast h_key
      _ = (E_sub.card : ℝ) ^ 2 := by push_cast; ring
  have h_bound : (𝒯_sub.card : ℝ) ≤ 4 * (E_sub.card : ℝ) ^ 2 / R ^ 2 := by
    rw [le_div_iff₀ hR2_pos]
    linarith
  have h_Esub_sq : (E_sub.card : ℝ) ^ 2 ≤ Rtilde ^ 2 := by
    apply sq_le_sq'
    · linarith [Nat.cast_nonneg (α := ℝ) E_sub.card]
    · exact hE_sub_card
  calc (𝒯_sub.card : ℝ)
    ≤ 4 * (E_sub.card : ℝ) ^ 2 / R ^ 2 := h_bound
    _ ≤ 4 * Rtilde ^ 2 / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ R ^ 2)
      linarith

end ProjectionTheory

namespace ProjectionTheory

/--
[log_dominated_by_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/GSW.lean)
-/
@[path]
lemma log_dominated_by_rpow
  {ε : ℝ}
  {δ : ℝ}
-- given
  (hε : 0 < ε)
  (hδ : 0 < δ)
  (hδ1 : δ ≤ 1) :
-- imply
  1 + Real.log (1 / δ) / Real.log 2 ≤ (1 + 1 / (ε * Real.log 2)) * δ ^ (-ε) := by
-- proof
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hδε_ge_1 : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ)]
    exact Bound.one_le_inv₀ (Real.rpow_pos_of_pos hδ ε)
      (Real.rpow_le_one (le_of_lt hδ) hδ1 (le_of_lt hε))
  have hδ_inv_nonneg : (0 : ℝ) ≤ 1 / δ := by positivity
  have hlog_bound : Real.log (1 / δ) ≤ (1 / δ) ^ ε / ε :=
    Real.log_le_rpow_div hδ_inv_nonneg hε
  have hpow_eq : (1 / δ) ^ ε = δ ^ (-ε) := by
    rw [one_div, Real.inv_rpow (le_of_lt hδ), Real.rpow_neg (le_of_lt hδ)]
  rw [hpow_eq] at hlog_bound
  have hmul : Real.log (1 / δ) * ε ≤ δ ^ (-ε) := by
    rwa [le_div_iff₀ hε] at hlog_bound
  have hlog_div : Real.log (1 / δ) / Real.log 2 ≤ δ ^ (-ε) / (ε * Real.log 2) := by
    rw [div_le_div_iff₀ hlog2_pos (by positivity : (0:ℝ) < ε * Real.log 2)]
    nlinarith
  have hexpand : (1 + 1 / (ε * Real.log 2)) * δ ^ (-ε) =
    δ ^ (-ε) + δ ^ (-ε) / (ε * Real.log 2) := by ring
  rw [hexpand]
  linarith
/-- **Theorem (GSW).** Let `E ⊂ ℝ²` be a set of `N` `δ`-balls in `B₁` which is well-spaced
(every ball of radius `N^(-1/2)` meets `E` in `≲ 1` points). Let `𝒯_R(E)` be a family of
essentially distinct `δ`-tubes with `|T ∩ E|_δ ≥ R`, and assume `R > δ^(-ε) · δ · |E|_δ`.
Then $|\mathcal T_R(E)| \lessapprox N^2 / R^3$, formalised here as
$|\mathcal T| \le C_\varepsilon \, \delta^{-\varepsilon} |E|^2 / R^3$. -/
end ProjectionTheory



-- created on 2026-10-23
