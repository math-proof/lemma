import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    g' ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus := by
  intro x' hx'
  set U : X.Opens := f.smoothLocus with hUdef
  let _ : LocallyOfFinitePresentation (U.ι ≫ f) := inferInstance
  have hU : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq U.ι f]
    exact Scheme.Opens.ι_preimage_self U
  have sq : IsPullback (g' ∣_ U) ((g' ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) g :=
    (isPullback_morphismRestrict g' U).paste_vert h
  let _ : LocallyOfFinitePresentation ((g' ⁻¹ᵁ U).ι ≫ f') := inferInstance
  have hU' : Smooth ((g' ⁻¹ᵁ U).ι ≫ f') := MorphismProperty.of_isPullback (P := @Smooth) sq hU
  have htop : (g' ⁻¹ᵁ U).ι ⁻¹ᵁ f'.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (g' ⁻¹ᵁ U).ι f', Scheme.Hom.smoothLocus_eq_top_iff]
    exact hU'
  have hmem : (⟨x', hx'⟩ : ↥(g' ⁻¹ᵁ U)) ∈ (g' ⁻¹ᵁ U).ι ⁻¹ᵁ f'.smoothLocus := by
    rw [htop]; trivial
  exact hmem
/--
[AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback.lean)
-/
@[path]
private lemma main
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    g' ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus :=
  AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_of_isPullback h


-- created on 2026-10-20
