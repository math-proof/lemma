import Mathlib
import sympy.Basic
open Set MeasureTheory



@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Icc a b)) :
-- imply
  ∃ ε ∈ Ioo (0 : ℝ) 1, ∫ x in a..b, f x = (b - a) * f (a * ε + b * (1 - ε)) := by
-- proof
  obtain rfl | hab' := hab.eq_or_lt
  ·
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp
  ·
    have hb0 : b - a ≠ 0 := sub_ne_zero.mpr hab'.ne'
    have hfc : ∀ t ∈ Ioo a b, ContinuousAt f t := fun t ht => hf.continuousAt (Icc_mem_nhds ht.1 ht.2)
    set A := (∫ x in a..b, f x) / (b - a) with hA
    have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun u => ∫ x in a..u, f x) (f t) t := by
      intro t ht
      apply intervalIntegral.integral_hasDerivAt_right _ _ (hfc t ht)
      ·
        apply ContinuousOn.intervalIntegrable_of_Icc ht.1.le
        apply hf.mono
        apply Icc_subset_Icc le_rfl ht.2.le
      ·
        apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hfc t ht
    set g := fun t => (∫ x in a..t, f x) - (t - a) * A with hg
    have hdiff : ∀ t ∈ Ioo a b, HasDerivAt g (f t - A) t := by
      intro t ht
      apply HasDerivAt.sub (hderiv t ht)
      simpa using ((hasDerivAt_id' t).sub_const a).mul_const A
    have hprim : ContinuousOn (fun u => ∫ x in a..u, f x) (Icc a b) := by
      have hint : IntegrableOn f (uIcc a b) volume := by
        rw [uIcc_of_le hab]
        apply hf.integrableOn_Icc
      have hcont := intervalIntegral.continuousOn_primitive_interval hint
      rwa [uIcc_of_le hab] at hcont
    have hgc : ContinuousOn g (Icc a b) := by
      apply ContinuousOn.sub hprim
      apply ContinuousOn.mul
      ·
        apply ContinuousOn.sub continuousOn_id continuousOn_const
      ·
        apply continuousOn_const
    have hgI : g a = g b := by
      have hga : g a = 0 := by
        simp [hg, intervalIntegral.integral_same]
      have hgb : g b = 0 := by
        simp only [hg, hA]
        rw [mul_div_cancel₀ _ hb0]
        simp
      rw [hga, hgb]
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab' hgc hgI hdiff
    have hfcA : f c = A := by
      apply sub_eq_zero.mp hc0
    refine ⟨(c - b) / (a - b), ⟨?_, ?_⟩, ?_⟩
    ·
      apply div_pos_of_neg_of_neg
      ·
        linarith [hc.2]
      ·
        linarith [hab']
    ·
      apply (div_lt_iff_of_neg _).mpr
      ·
        linarith [hc.1]
      ·
        linarith [hab']
    ·
      have hp : a * ((c - b) / (a - b)) + b * (1 - (c - b) / (a - b)) = c := by
        have hneg : a - b ≠ 0 := sub_ne_zero.mpr hab'.ne
        field_simp [hneg]
        ring
      rw [hp, hfcA, hA, mul_div_cancel₀ _ hb0]


-- created on 2026-10-07
