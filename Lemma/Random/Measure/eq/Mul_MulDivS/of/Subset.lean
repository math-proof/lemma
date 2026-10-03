import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import sympy.Basic
open MeasureTheory


/--
Chain rule for the measure of a nested event under the two one-step conditional independences
(`E ⟂ C | F` and `F ⟂ C' | G`, `C = C' ∩ G`), stated for measures so that no events of
probability `0` need to be excluded:
`π (C ∩ F ∩ E) = π C * (π (F ∩ G) / π G * (π (E ∩ F) / π F))`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {C E F G : Set Ω}
-- given
  (hC : C ⊆ G)
  (h₁ : π (E ∩ C ∩ F) * π F = π (E ∩ F) * π (C ∩ F))
  (h₂ : π (F ∩ C) * π G = π (F ∩ G) * π C) :
-- imply
  π (C ∩ F ∩ E) = π C * (π (F ∩ G) / π G * (π (E ∩ F) / π F)) := by
-- proof
  have e : C ∩ F ∩ E = E ∩ C ∩ F := by
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have e' : F ∩ C = C ∩ F := Set.inter_comm F C
  rw [e]
  rw [e'] at h₂
  if hG : π G = 0 then
    have hC0 : π C = 0 := measure_mono_null hC hG
    have h0 : π (E ∩ C ∩ F) = 0 := measure_mono_null (fun ω hω => hω.1.2) hC0
    rw [h0, hC0, zero_mul]
  else if hF : π F = 0 then
    have h0 : π (E ∩ C ∩ F) = 0 := measure_mono_null (fun ω hω => hω.2) hF
    have hFG : π (F ∩ G) = 0 := measure_mono_null Set.inter_subset_left hF
    rw [h0, hFG, ENNReal.zero_div, zero_mul, mul_zero]
  else
    have hG' : π G ≠ ⊤ := measure_ne_top _ _
    have hF' : π F ≠ ⊤ := measure_ne_top _ _
    have hT : π (E ∩ C ∩ F) = π (E ∩ F) * π (C ∩ F) * (π F)⁻¹ := by
      rw [← h₁, mul_assoc, ENNReal.mul_inv_cancel hF hF', mul_one]
    have hCF : π (C ∩ F) = π (F ∩ G) * π C * (π G)⁻¹ := by
      rw [← h₂, mul_assoc, ENNReal.mul_inv_cancel hG hG', mul_one]
    rw [hT, hCF, div_eq_mul_inv, div_eq_mul_inv]
    ring


-- created on 2026-10-02