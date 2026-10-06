import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp.lean)
-/

private lemma  RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3
    {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  letI := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
@[main]
private lemma main
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} [Smooth f]
  {x : X} :
-- imply
  ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
-- proof
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3 hstd
  refine ⟨V, d, hx, ?_⟩

  have hres : SmoothOfRelativeDimension d (f.resLE U V e) := by
    haveI : IsAffine V := hV
    haveI : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have := (RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))))
    refine ((MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))) (arrowResLEAppIso f U V e)).mpr ?_)
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _ hd
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  simpa using this


-- created on 2026-10-05
