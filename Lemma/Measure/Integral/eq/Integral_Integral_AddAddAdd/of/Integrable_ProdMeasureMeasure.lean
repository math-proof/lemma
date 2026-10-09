import Mathlib
import sympy.Basic

open MeasureTheory Set

/--
[LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections.lean)
-/

private lemma  fold₁ (f : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ)) :
    ∫ t : ℝ, f t = ∫ t in Set.Ioi (0 : ℝ), (f t + f (-t)) := by
  rw [integral_add hf.integrableOn hf.comp_neg.integrableOn, integral_comp_neg_Ioi, neg_zero,
    ← integral_add_compl measurableSet_Ioi hf, compl_Ioi]
@[path]
private lemma main
  {F : ℝ × ℝ → ℂ}
-- given
  (hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
-- imply
  ∫ p : ℝ × ℝ, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), (F (t, y) + F (-t, y) + F (t, -y) + F (-t, -y)) := by
-- proof
  have eG : ∫ x : ℝ, (∫ y : ℝ, F (x, y)) =
      ∫ t in Set.Ioi (0 : ℝ), ((∫ y : ℝ, F (t, y)) + ∫ y : ℝ, F (-t, y)) :=
    fold₁ (fun x => ∫ y : ℝ, F (x, y)) hF.integral_prod_left
  rw [integral_prod F hF, eG]
  have h1 : ∀ᵐ t : ℝ, Integrable (fun y : ℝ => F (t, y)) (volume : Measure ℝ) := hF.prod_right_ae
  have h2 : ∀ᵐ t : ℝ, Integrable (fun y : ℝ => F (-t, y)) (volume : Measure ℝ) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h1, h2] with t ht1 ht2
  have e1 : ∫ y : ℝ, F (t, y) = ∫ y in Set.Ioi (0 : ℝ), (F (t, y) + F (t, -y)) := fold₁ _ ht1
  have e2 : ∫ y : ℝ, F (-t, y) = ∫ y in Set.Ioi (0 : ℝ), (F (-t, y) + F (-t, -y)) := fold₁ _ ht2
  have hA : Integrable (fun y : ℝ => F (t, y) + F (t, -y)) (volume : Measure ℝ) := ht1.add ht1.comp_neg
  have hB : Integrable (fun y : ℝ => F (-t, y) + F (-t, -y)) (volume : Measure ℝ) := ht2.add ht2.comp_neg
  rw [e1, e2, ← integral_add hA.integrableOn hB.integrableOn]
  congr 1
  funext y
  ring


-- created on 2026-10-05
