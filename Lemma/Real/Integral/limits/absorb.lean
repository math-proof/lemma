import Mathlib
import sympy.Basic

open MeasureTheory Set Filter


@[main]
private lemma main
  {a : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x in Ioi 0, f x * (if x ∈ Icc (-a) a then (1 : ℝ) else 0) = ∫ x in Ioc 0 a, f x := by
-- proof
  if ha : 0 < a then
    have h : (Ioi 0).indicator (fun x => f x * (if x ∈ Icc (-a) a then (1 : ℝ) else 0)) = (Ioc 0 a).indicator f := by
      ext x
      simp only [Set.indicator, mem_Ioc, mem_Icc, mem_Ioi]
      split_ifs <;> grind
    rw [← integral_indicator measurableSet_Ioi]
    rw [h]
    apply integral_indicator measurableSet_Ioc
  else
    have ha_nonpos : a ≤ 0 := by linarith
    have h0 : Ioc 0 a = ∅ := by
      ext x
      simp [mem_Ioc]
      intro h1
      linarith
    rw [h0, setIntegral_empty]
    apply integral_eq_zero_of_ae
    show ∀ᵐ x ∂(volume.restrict (Ioi 0)), (fun x => f x * (if x ∈ Icc (-a) a then (1 : ℝ) else 0)) x = 0
    rw [ae_restrict_iff' measurableSet_Ioi]
    apply Eventually.of_forall
    intro x hx
    simp only [mem_Ioi] at hx
    have hmem : x ∉ Icc (-a) a := by
      simp only [mem_Icc, not_and_or]
      right
      linarith
    simp [hmem]


-- created on 2026-10-07
