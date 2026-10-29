import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped ENNReal
open MeasureTheory


private lemma map_zero_of_forall_map_add
  {G X : Type*}
  [Group G]
  [MeasurableSpace G]
  [MeasurableMul₂ G]
  [AddGroup X]
  [MeasurableSpace X]
  [MeasurableNeg X]
  (n : X → G) (hn : ∀ x y, n (x + y) = n x * n y) : n 0 = 1 := by
  have h := hn 0 0
  rw [add_zero] at h
  exact ((left_eq_mul.1 h).symm).symm

private lemma map_neg_mul
  {G X : Type*}
  [Group G]
  [MeasurableSpace G]
  [MeasurableMul₂ G]
  [AddGroup X]
  [MeasurableSpace X]
  [MeasurableNeg X]
  (n : X → G) (hn : ∀ x y, n (x + y) = n x * n y) (x : X) : n (-x) * n x = 1 := by
  rw [← hn, neg_add_cancel, map_zero_of_forall_map_add n hn]

private lemma helper_main
  {G X : Type*}
  [Group G]
  [MeasurableSpace G]
  [MeasurableMul₂ G]
  [AddGroup X]
  [MeasurableSpace X]
  [MeasurableNeg X]
  (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
  (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
  (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
  (Φ : G → ENNReal) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
  (w w₀ : G → ENNReal) (hw : Measurable w) (hw₀ : Measurable w₀)
  (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
  ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ := by
  have hF : Measurable fun p : G × X => w p.1 * Φ p.1 * w₀ (p.1 * n p.2) :=
    ((hw.comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
      (hw₀.comp (measurable_fst.mul (hn.comp measurable_snd)))
  have hF' : Measurable fun p : G × X => w (p.1 * n (-p.2)) * Φ p.1 * w₀ p.1 :=
    ((hw.comp (measurable_fst.mul (hn.comp measurable_snd.neg))).mul (hΦ.comp measurable_fst)).mul
      (hw₀.comp measurable_fst)
  calc
    _ = ∫⁻ g, w g * Φ g * ∫⁻ x, w₀ (g * n x) ∂μ ∂τ :=
      lintegral_congr_ae (h1₀.mono fun g hg => by simp only [hg, mul_one])
    _ = ∫⁻ g, ∫⁻ x, w g * Φ g * w₀ (g * n x) ∂μ ∂τ := by
      refine lintegral_congr fun g => ?_
      have hm : Measurable fun x => w₀ (g * n x) := hw₀.comp ((measurable_const_mul g).comp hn)
      rw [lintegral_const_mul _ hm]
    _ = ∫⁻ x, ∫⁻ g, w g * Φ g * w₀ (g * n x) ∂τ ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x, ∫⁻ g, w (g * n (-x)) * Φ g * w₀ g ∂τ ∂μ := by
      refine lintegral_congr fun x => ?_
      rw [← lintegral_mul_right_eq_self (fun g => w g * Φ g * w₀ (g * n x)) (n (-x))]
      refine lintegral_congr fun g => ?_
      simp only [mul_assoc, map_neg_mul n hn_add, mul_one, hΦn]
    _ = ∫⁻ g, ∫⁻ x, w (g * n (-x)) * Φ g * w₀ g ∂μ ∂τ := (lintegral_lintegral_swap hF'.aemeasurable).symm
    _ = ∫⁻ g, (∫⁻ x, w (g * n (-x)) ∂μ) * (Φ g * w₀ g) ∂τ := by
      refine lintegral_congr fun g => ?_
      have hm : Measurable fun x => w (g * n (-x)) :=
        hw.comp ((measurable_const_mul g).comp (hn.comp measurable_neg))
      rw [← lintegral_mul_const _ hm]
      refine lintegral_congr fun x => ?_
      rw [mul_assoc]
    _ = ∫⁻ g, (∫⁻ x, w (g * n x) ∂μ) * (Φ g * w₀ g) ∂τ := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_neg_eq_self (μ := μ) (fun x => w (g * n x))]
    _ = ∫⁻ g, w₀ g * Φ g ∂τ :=
        lintegral_congr_ae (h1.mono fun g hg => by simp only [hg, one_mul]; exact mul_comm _ _)
/--
[MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one.lean)
-/
@[path]
private lemma main
  [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
  {τ : Measure G} [SFinite τ] [τ.IsMulRightInvariant]
  {μ : Measure X} [SFinite μ] [μ.IsNegInvariant]
  {n : X → G}
-- given
  (Φ w w₀ : G → ENNReal)
  (hn : Measurable n)
  (hn_add : ∀ x y, n (x + y) = n x * n y)
  (hΦ : Measurable Φ)
  (hΦn : ∀ g x, Φ (g * n x) = Φ g)
  (hw : Measurable w)
  (hw₀ : Measurable w₀)
  (hone : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1)
  (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
-- imply
  ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ :=
-- proof
  helper_main τ μ n hn hn_add Φ hΦ hΦn w w₀ hw hw₀ hone h1₀


-- created on 2026-10-23
