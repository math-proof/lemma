import sympy.integrals.integrals
import sympy.Basic
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory


@[main]
private lemma main
  {a b c d : ℝ}
  {f : ℝ → ℝ}
  {g : ℝ → ℝ → ℝ}
-- given
  (hf : Continuous f)
  (hgu : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
-- imply
  ∫ x : ℝ in a..b, ∫ y : ℝ in c..d, f x * g x y = ∫ y : ℝ in c..d, ∫ x : ℝ in a..b, f x * g x y := by
-- proof
  have hc : Continuous fun p : ℝ × ℝ => f p.1 * g p.1 p.2 :=
    (hf.comp continuous_fst).mul hgu
  have hF : IntegrableOn (fun p : ℝ × ℝ => f p.1 * g p.1 p.2) (Set.uIoc a b ×ˢ Set.uIoc c d) :=
    (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap hF


-- created on 2026-09-26
