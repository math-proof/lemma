import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ Z)
    (hψK : ψK ≫ ι = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ ι = φ := by
  let _ : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
    have hinj : Function.Injective (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom := by
      have e : (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop =
          (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R K) ≫
            (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
        rw [← Iso.inv_comp_eq]
        exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))).symm
      have i1 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      have i2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        RingHom.coe_comp]
      exact (i1.comp (IsFractionRing.injective R K)).comp i2
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [Scheme.IdealSheafData.ideal_bot]
  let _ : IsSchemeTheoreticallyDominant
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := inferInstance
  have H : ι.ker ≤ φ.ker := by
    change ι.ker ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (φ.app U).hom
    rw [Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U s hs
    have hs0 : ι.app U s = 0 := ι.ideal_ker_le U hs
    rw [RingHom.mem_ker]
    apply (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app_injective
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_app,
      Scheme.Hom.congr_app hψK.symm U, Scheme.Hom.comp_app]
    simp [hs0]
  refine ⟨IsClosedImmersion.lift ι φ H, IsClosedImmersion.lift_fac ι φ H, ?_⟩
  intro ψ hψ
  rw [← cancel_mono ι, hψ, IsClosedImmersion.lift_fac]

-- created on 2026-10-20
