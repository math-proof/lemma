import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.MultConvLinftyBound
open Finset Complex BigOperators HighFreqMultConv


namespace HighFreqMultConv

/--
[mulConvUnits_eq_mulConv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma mulConvUnits_eq_mulConv
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {f g : (ZMod q)ˣ → ℂ}
  {a : (ZMod q)ˣ} :
-- imply
  mulConvUnits q f g a = MultiplicativeConvolution.mulConv f g a := by
-- proof
  simp only [mulConvUnits, MultiplicativeConvolution.mulConv, div_eq_mul_inv]

end HighFreqMultConv

namespace HighFreqMultConv

/--
[l2NormUnits_eq_l2Norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma l2NormUnits_eq_l2Norm
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {f : (ZMod q)ˣ → ℂ} :
-- imply
  l2NormUnits q f = MultiplicativeConvolution.l2Norm f := by
-- proof
  simp only [l2NormUnits, MultiplicativeConvolution.l2Norm]

end HighFreqMultConv

namespace HighFreqMultConv

/--
[norm_highFreq_mulConvUnits_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma norm_highFreq_mulConvUnits_le
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {f g : (ZMod q)ˣ → ℂ}
  {a : (ZMod q)ˣ} :
-- imply
  ‖highFreqUnits q (mulConvUnits q f g) a‖ ≤ l2NormUnits q (highFreqUnits q f) * l2NormUnits q (highFreqUnits q g) := by
-- proof
  have h4 := highFreq_mulConvUnits q f g
  rw [show highFreqUnits q (mulConvUnits q f g) a =
    mulConvUnits q (highFreqUnits q f) (highFreqUnits q g) a from
    congr_fun h4 a]
  rw [mulConvUnits_eq_mulConv]
  rw [l2NormUnits_eq_l2Norm, l2NormUnits_eq_l2Norm]
  exact MultiplicativeConvolution.norm_mulConv_le _ _ a

end HighFreqMultConv

namespace HighFreqMultConv

/--
[highFreq_mulConv_linfty_le_l2_l2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma highFreq_mulConv_linfty_le_l2_l2
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {f g : (ZMod q)ˣ → ℂ} :
-- imply
  (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q (mulConvUnits q f g) a‖) ≤ l2NormUnits q (highFreqUnits q f) * l2NormUnits q (highFreqUnits q g) := by
-- proof
  apply ciSup_le
  exact norm_highFreq_mulConvUnits_le q f g

end HighFreqMultConv

namespace HighFreqMultConv

/--
[mulConv_ZMod_units_eq_mulConvUnits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma mulConv_ZMod_units_eq_mulConvUnits
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {F G : ZMod q → ℂ}
  {u : (ZMod q)ˣ} :
-- imply
  MultiplicativeConvolution.mulConv_ZMod q F G (↑u : ZMod q) = mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) u := by
-- proof
  simp only [MultiplicativeConvolution.mulConv_ZMod, mulConvUnits, restrictToUnits]
  have hu_ne : (↑u : ZMod q) ≠ 0 := Units.ne_zero u
  have h_inner : ∀ b : ZMod q,
    (∑ c : ZMod q, if b * c = (↑u : ZMod q) then F b * G c else 0) =
    if b ≠ 0 then F b * G ((↑u : ZMod q) * b⁻¹) else 0 := by
    intro b
    by_cases hb : b = 0
    · subst hb
      simp only [zero_mul, ne_eq, not_true, ite_false]
      apply Finset.sum_eq_zero; intro c _
      simp [hu_ne.symm]
    · simp only [hb, ne_eq, not_false_eq_true, ite_true]
      have hiff : ∀ c : ZMod q, (b * c = (↑u : ZMod q)) ↔ (c = (↑u : ZMod q) * b⁻¹) := by
        intro c
        constructor
        · intro h
          have h1 : c = b⁻¹ * (↑u : ZMod q) := by
            have := congr_arg (b⁻¹ * ·) h
            simp only [← mul_assoc, inv_mul_cancel₀ hb, one_mul] at this
            exact this
          rw [h1, mul_comm]
        · intro h
          rw [h, mul_comm (↑u : ZMod q) b⁻¹, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      conv_lhs => arg 2; ext c; rw [show (if b * c = ↑u then F b * G c else 0) =
        (if c = (↑u : ZMod q) * b⁻¹ then F b * G c else 0) from by
        congr 1; exact propext (hiff c)]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
  simp_rw [h_inner]
  have h_filter : (∑ b : ZMod q, if b ≠ 0 then F b * G (↑u * b⁻¹) else 0) =
    ∑ b ∈ univ.filter (fun b : ZMod q => b ≠ 0), F b * G (↑u * b⁻¹) := by
    rw [Finset.sum_filter]
  rw [h_filter]
  have h_image : univ.filter (fun b : ZMod q => b ≠ 0) =
    univ.image (fun v : (ZMod q)ˣ => (↑v : ZMod q)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_image]
    exact ⟨fun hx => ⟨Units.mk0 x hx, rfl⟩,
      fun ⟨v, hv⟩ => hv ▸ Units.ne_zero v⟩
  rw [h_image, Finset.sum_image (by intro a _ b _ h; exact Units.ext h)]
  congr 1; ext b; congr 1
  rw [Units.val_div_eq_div_val, div_eq_mul_inv]

end HighFreqMultConv

namespace HighFreqMultConv

/--
[restrictToUnits_mulConv_ZMod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma restrictToUnits_mulConv_ZMod_eq
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {F G : ZMod q → ℂ} :
-- imply
  restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q F G) = mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) := by
-- proof
  funext u
  exact mulConv_ZMod_units_eq_mulConvUnits q F G u

end HighFreqMultConv

namespace HighFreqMultConv

/--
[l2NormUnits_highFreq_restrict_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma l2NormUnits_highFreq_restrict_le
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {F : ZMod q → ℂ} :
-- imply
  l2NormUnits q (highFreqUnits q (restrictToUnits q F)) ≤ l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q F) := by
-- proof
  unfold l2NormUnits l2Norm_ZMod LinnikLargeSieve.l2NormSq_ZMod
  apply Real.sqrt_le_sqrt
  show ∑ u : (ZMod q)ˣ, ‖highFreqUnits q (restrictToUnits q F) u‖ ^ 2 ≤
    ∑ a : ZMod q, ‖LinnikLargeSieve.highFreqPart_ZMod q F a‖ ^ 2
  simp only [highFreqUnits, restrictToUnits, LinnikLargeSieve.highFreqPart_ZMod]
  set μ := (1 / (q : ℂ)) * ∑ b : ZMod q, F b
  set μ_star := (∑ v : (ZMod q)ˣ, F (↑v)) / (Fintype.card (ZMod q)ˣ : ℂ)
  have h_zero : ∑ u : (ZMod q)ˣ, (F (↑u) - μ_star) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, μ_star]
    have hn : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp; ring
  have h_min : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ_star‖ ^ 2 ≤
    ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 := by
    have h_diff : ∀ u : (ZMod q)ˣ,
      ‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2 =
      ‖μ_star - μ‖ ^ 2 + 2 * @inner ℝ ℂ _ (F (↑u) - μ_star) (μ_star - μ) := by
      intro u
      have : F (↑u) - μ = (F (↑u) - μ_star) + (μ_star - μ) := by ring
      rw [this, norm_add_sq_real]; ring
    have h_sum_diff : ∑ u : (ZMod q)ˣ, (‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2) =
      (Fintype.card (ZMod q)ˣ : ℝ) * ‖μ_star - μ‖ ^ 2 := by
      simp_rw [h_diff, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      have h_cross : ∑ u : (ZMod q)ˣ, @inner ℝ ℂ _ (F (↑u) - μ_star) (μ_star - μ) = 0 := by
        rw [← sum_inner (𝕜 := ℝ), h_zero, inner_zero_left]
      linarith [h_cross]
    have h_nonneg : 0 ≤ ∑ u : (ZMod q)ˣ, (‖F (↑u) - μ‖ ^ 2 - ‖F (↑u) - μ_star‖ ^ 2) := by
      rw [h_sum_diff]
      exact mul_nonneg (Nat.cast_nonneg' _) (sq_nonneg _)
    linarith [Finset.sum_sub_distrib
      (f := fun u : (ZMod q)ˣ => ‖F (↑u) - μ‖ ^ 2)
      (g := fun u : (ZMod q)ˣ => ‖F (↑u) - μ_star‖ ^ 2)
      (s := Finset.univ)]
  have h_subset : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 ≤
    ∑ a : ZMod q, ‖F a - μ‖ ^ 2 := by
    have h_eq : ∑ u : (ZMod q)ˣ, ‖F (↑u) - μ‖ ^ 2 =
      ∑ a ∈ univ.filter (fun x : ZMod q => x ≠ 0), ‖F a - μ‖ ^ 2 := by
      rw [show univ.filter (fun x : ZMod q => x ≠ 0) =
        univ.image (fun v : (ZMod q)ˣ => (↑v : ZMod q)) from by
        ext x; simp only [mem_filter, mem_univ, true_and, mem_image]
        exact ⟨fun hx => ⟨Units.mk0 x hx, rfl⟩, fun ⟨v, hv⟩ => hv ▸ Units.ne_zero v⟩]
      rw [Finset.sum_image (by intro a _ b _ h; exact Units.ext h)]
    rw [h_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro a _ _; positivity
  linarith

end HighFreqMultConv

namespace HighFreqMultConv

/--
[highFreq_mulConv_linfty_le_l2_l2_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean)
-/
@[path]
lemma highFreq_mulConv_linfty_le_l2_l2_full
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {N : ℕ}
  {f g : ℕ → ℂ}
-- given
  (_hf : ∀ n, N ≤ n → f n = 0)
  (_hg : ∀ n, N ≤ n → g n = 0)
  (_hf0 : f 0 = 0)
  (_hg0 : g 0 = 0) :
-- imply
  (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q (restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q (MultiplicativeConvolution.modProjection_arith N q f) (MultiplicativeConvolution.modProjection_arith N q g))) a‖) ≤ l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q (MultiplicativeConvolution.modProjection_arith N q f)) * l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q (MultiplicativeConvolution.modProjection_arith N q g)) := by
-- proof
  set F := MultiplicativeConvolution.modProjection_arith N q f
  set G := MultiplicativeConvolution.modProjection_arith N q g
  have h_restrict : restrictToUnits q (MultiplicativeConvolution.mulConv_ZMod q F G) =
    mulConvUnits q (restrictToUnits q F) (restrictToUnits q G) :=
    restrictToUnits_mulConv_ZMod_eq q F G
  simp_rw [h_restrict]
  have step2 := highFreq_mulConv_linfty_le_l2_l2 q (restrictToUnits q F) (restrictToUnits q G)
  have step3f := l2NormUnits_highFreq_restrict_le q F
  have step3g := l2NormUnits_highFreq_restrict_le q G
  calc (⨆ a : (ZMod q)ˣ, ‖highFreqUnits q
    (mulConvUnits q (restrictToUnits q F) (restrictToUnits q G)) a‖)
    ≤ l2NormUnits q (highFreqUnits q (restrictToUnits q F)) *
      l2NormUnits q (highFreqUnits q (restrictToUnits q G)) := step2
    _ ≤ l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q F) *
      l2Norm_ZMod q (LinnikLargeSieve.highFreqPart_ZMod q G) := by
      apply mul_le_mul step3f step3g
      · unfold l2NormUnits; positivity
      · unfold l2Norm_ZMod LinnikLargeSieve.l2NormSq_ZMod; positivity

end HighFreqMultConv


-- created on 2026-10-23
