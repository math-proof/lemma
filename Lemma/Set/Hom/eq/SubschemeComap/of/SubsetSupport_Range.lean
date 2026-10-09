import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range.lean)
-/
@[path]
private lemma main
  {X Y : Scheme.{u}}
  {I : X.IdealSheafData}
  {ψ : Y ⟶ X} [IsOpenImmersion ψ]
-- given
  (h : (I.support : Set X) ⊆ Set.range ψ) :
-- imply
  ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ := by
-- proof
  have hZU : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range ⇑ψ := by
    intro z
    apply h
    change I.subschemeι z ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  have : IsIso (pullback.snd ψ I.subschemeι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  refine ⟨I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]


-- created on 2026-10-05
