import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

/--
[CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.lean)
-/
@[main]
private lemma main
  {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C] [CategoryTheory.HasExt.{w} C]
  {S : CategoryTheory.ShortComplex C}
-- given
  (hS : S.ShortExact) :
-- imply
  hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
-- proof
  constructor
  · intro h0
    have hx : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp, h0]
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) hx
    refine ⟨Ext.homEquiv₀ x₂, ?_⟩
    have : Ext.mk₀ (Ext.homEquiv₀ x₂ ≫ S.g) = Ext.mk₀ (𝟙 S.X₃) := by
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply, hx₂]
    exact Ext.homEquiv₀.symm.injective (by simpa [Ext.mk₀_homEquiv₀_apply] using this)
  · rintro ⟨s, hs⟩
    have h1 : (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) = 0 := by
      rw [hS.comp_extClass, Ext.comp_zero]
    rwa [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs, Ext.mk₀_id_comp] at h1


-- created on 2026-10-05
