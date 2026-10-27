import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.X1
import Lemma.ModularCurve.LaurentCoeff
import Lemma.Int.P2MUtil

open ModularCurve
open scoped MatrixGroups

/--
[ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap.lean)
-/
@[path]
private lemma main
  {k₀ k : Type*} [Field k₀] [Field k]
  {σ : k₀ →+* k}
  {Γ : Subgroup SL(2, ℤ)} :
-- imply
  ∃ ι : ↥(ModularCurve.qExpFunctionFieldC k₀ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ∀ x : ↥(ModularCurve.qExpFunctionFieldC k₀ Γ),
        ((ι x : ↥(ModularCurve.qExpFunctionFieldC k Γ)) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀) := by
  classical
  set φ : LaurentSeries k₀ →+* LaurentSeries k := coeffMap σ with hφ
  have hint : ∀ p : PowerSeries ℤ, φ (intSeriesC k₀ p) = intSeriesC k p := by
-- proof
    intro p
    ext n
    rw [hφ, coeffMap_coeff, intSeriesC, intSeriesC]
    rcases le_or_gt 0 n with hn | hn
    ·
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
    · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  have hgen : ∀ x ∈ intFormRatiosC k₀ Γ, φ x ∈ intFormRatiosC k Γ := by
    rintro x ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hg0' : intSeriesC k pg ≠ 0 := by rw [← hint]; exact (map_ne_zero φ).mpr hg0
    refine ⟨w, f, g, pf, pg, hf, hg, hg0', ?_⟩
    rw [map_div₀, hint, hint]
  have hconst : ∀ a : k₀, φ (algebraMap k₀ (LaurentSeries k₀) a) = algebraMap k (LaurentSeries k) (σ a) := by
    intro a
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, hφ, coeffMap_single]
  have hcl : ∀ y : LaurentSeries k₀,
      y ∈ Subfield.closure (Set.range (algebraMap k₀ (LaurentSeries k₀)) ∪ intFormRatiosC k₀ Γ) →
      φ y ∈ ModularCurve.qExpFunctionFieldC k Γ := by
    intro y hy
    induction hy using Subfield.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      ·
        rw [hconst]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin _ _ (hgen y hy)
    | one => rw [map_one]; exact IntermediateField.one_mem _
    | add y z _ _ hy hz => rw [map_add]; exact IntermediateField.add_mem _ hy hz
    | neg y _ hy => rw [map_neg]; exact IntermediateField.neg_mem _ hy
    | inv y _ hy => rw [map_inv₀]; exact IntermediateField.inv_mem _ hy
    | mul y z _ _ hy hz => rw [map_mul]; exact IntermediateField.mul_mem _ hy hz
  have hmap : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k₀ Γ), φ x ∈ ModularCurve.qExpFunctionFieldC k Γ := by
    intro x
    apply hcl
    rw [← IntermediateField.adjoin_toSubfield]; exact x.2
  refine ⟨RingHom.codRestrict (φ.comp (ModularCurve.qExpFunctionFieldC k₀ Γ).toSubfield.subtype)
    (ModularCurve.qExpFunctionFieldC k Γ) (fun x => hmap x), fun x => rfl⟩


-- created on 2026-10-23
