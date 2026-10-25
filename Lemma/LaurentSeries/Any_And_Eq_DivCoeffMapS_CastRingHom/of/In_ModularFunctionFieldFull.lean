import Mathlib
import sympy.Basic
import Lemma.ModularCurve.JqCoeff
import Lemma.ModularCurve.LaurentCoeff
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull.lean)
-/

private lemma  qExpand_coeffMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
  (x : LaurentSeries R) : qExpand S N (coeffMap f x) = coeffMap f (qExpand R N x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  ·
    obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, coeffMap_coeff, coeffMap_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd _ _ hk, coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hk, map_zero]

private lemma  jq_eq_coeffMap : jq = coeffMap (Int.castRingHom ℚ) (jqModC ℤ) := by
  rw [← jqModC_rat, jqModC_eq_map_intCast]; rfl

private lemma  qExpand_jq_mem_range (d : ℕ) [NeZero d] :
  qExpand ℚ d jq ∈ (coeffMap (Int.castRingHom ℚ)).range :=
  ⟨qExpand ℤ d (jqModC ℤ), by rw [jq_eq_coeffMap, qExpand_coeffMap]⟩

private lemma  adjoin_jq_le_range {x : LaurentSeries ℚ} (hx : x ∈ Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ))) :
  x ∈ (coeffMap (Int.castRingHom ℚ)).range := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := qExpand_jq_mem_range 1
    rwa [qExpand_one_apply] at this
  | algebraMap r =>
    refine ⟨(r : LaurentSeries ℤ), ?_⟩
    rw [map_intCast, eq_intCast]
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy


open in
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {x : LaurentSeries ℚ}
-- given
  (hx : x ∈ ModularCurve.modularFunctionFieldFull N) :
-- imply
  ∃ a b : LaurentSeries ℤ, b ≠ 0 ∧
      x = ModularCurve.coeffMap (Int.castRingHom ℚ) a / ModularCurve.coeffMap (Int.castRingHom ℚ) b := by
  classical
  set φ := coeffMap (Int.castRingHom ℚ) with hφ
  let S : Subfield (LaurentSeries ℚ) := Subfield.closure (Set.range φ)
  have hQ : ∀ q : ℚ, algebraMap ℚ (LaurentSeries ℚ) q ∈ S := fun q => by
    rw [eq_ratCast]; exact SubfieldClass.ratCast_mem S q
  let T : IntermediateField ℚ (LaurentSeries ℚ) := S.toIntermediateField hQ
  have hle : modularFunctionFieldFull N ≤ T := by
-- proof
    rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
    rintro _ ⟨d, hd, hdN, rfl⟩
    haveI := hd
    obtain ⟨y, hy⟩ := qExpand_jq_mem_range d
    exact Subfield.subset_closure ⟨y, hy⟩
  have hxS : x ∈ S := hle hx
  rw [Subfield.mem_closure_iff] at hxS
  obtain ⟨y, hy, z, hz, hyz⟩ := hxS
  have hcl : Subring.closure (Set.range φ) = φ.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hcl] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : b = 0
  ·
    refine ⟨0, 1, one_ne_zero, ?_⟩
    rw [map_zero, map_one, zero_div, ← hyz, hb, map_zero, div_zero]
  · exact ⟨a, b, hb, hyz.symm⟩


-- created on 2026-10-23
