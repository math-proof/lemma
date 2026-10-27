import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.LaurentCoeff
import Lemma.ModularCurve.JqCoeff
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_map_jqNModC](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_map_jqNModC.lean)
-/

private lemma  ModularCurve.solution_aux_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
  coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  ·
    obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]
@[path]
private lemma main
  {R S : Type*} [CommRing R] [CommRing S]
  {φ : R →+* S}
  {N : ℕ} [NeZero N] :
-- imply
  coeffMap φ (jqNModC R N) = jqNModC S N := by
-- proof
  have hj : coeffMap φ (jqModC R) = jqModC S := map_jqModC φ
  rw [jqNModC, jqNModC, ModularCurve.solution_aux_coeffMap_qExpand, hj]


-- created on 2026-10-23
