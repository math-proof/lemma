import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero.lean)
-/
@[path]
private lemma main
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S)) [IsClosedImmersion ι] :
    ∃ J : Ideal S, ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ ∀ x ∈ J, φ x = 0 := by
  obtain ⟨hZ, hsurj⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion) (f := ι)).mp inferInstance
  let _ : IsAffine Z := hZ
  set ψ₀ : S →+* Γ(Z, ⊤) := ι.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom with hψ₀def
  have hψ₀ : Function.Surjective ψ₀ := by
    rw [hψ₀def]
    exact hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv.surjective
  refine ⟨RingHom.ker ψ₀, fun R _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩ x hx
    have hx0 : ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom x) = 0 := hx
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ x) =
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom x) := by
      have := congrArg (fun k => k.hom x) hnat
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact this
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ x) = 0 := by
      rw [h1, ← hy, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hx0, map_zero]
    have h3 := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) h2
    simpa using h3
  · intro hJ
    let χ : Γ(Z, ⊤) →+* R :=
      (Ideal.Quotient.lift (RingHom.ker ψ₀) φ fun x hx => hJ x hx).comp
        (RingHom.quotientKerEquivOfSurjective hψ₀).symm.toRingHom
    have hχ : ∀ x : S, χ (ψ₀ x) = φ x := by
      intro x
      have he : (RingHom.quotientKerEquivOfSurjective hψ₀).symm (ψ₀ x) = Ideal.Quotient.mk (RingHom.ker ψ₀) x := by
        rw [RingEquiv.symm_apply_eq]
        exact (RingHom.quotientKerEquivOfSurjective_apply_mk hψ₀ x).symm
      show Ideal.Quotient.lift (RingHom.ker ψ₀) φ (fun x hx => hJ x hx) ((RingHom.quotientKerEquivOfSurjective hψ₀).symm (ψ₀ x)) = φ x
      rw [he, Ideal.Quotient.lift_mk]
    refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_⟩
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality ι, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    congr 1
    ext x
    change χ (ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom x)) = φ x
    exact hχ x


-- created on 2026-10-20
