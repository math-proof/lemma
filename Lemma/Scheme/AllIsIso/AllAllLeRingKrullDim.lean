import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of R)) :
  (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))), IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)) ∧ ∀ (n : ℕ), (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))), ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) ≤ n) → ∀ x : X, (f.base x).asIdeal = ⊥ → ringKrullDim (X.presheaf.stalk x) ≤ n := by
  let hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let _ : IsPreimmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  let _ : Flat (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hiso : ∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))), IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y) := by
    intro y
    set φ := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y
    have hsurj : Function.Surjective φ.hom :=
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap_surjective y
    have hinj : Function.Injective φ.hom := by
      have hfl : φ.hom.Flat := Flat.stalkMap _ y
      let A : Type u := ↑(X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y))
      let B : Type u := ↑((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y)
      have hloc : IsLocalHom φ.hom := inferInstance
      let _ : Algebra A B := φ.hom.toAlgebra
      let _ : Module.Flat A B := hfl
      let _ : IsLocalHom (algebraMap A B) := hloc
      apply (RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom).injective
    let _ : IsIso ((forget CommRingCat).map φ) := (isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    apply isIso_of_reflects_iso φ (forget CommRingCat)
  refine ⟨hiso, fun n hn x hx => ?_⟩
  let pt : ↥(Spec (CommRingCat.of K)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : f.base x = (Spec.map (CommRingCat.ofHom (algebraMap R K))).base pt := by
    apply PrimeSpectrum.ext
    rw [hx]
    change (⊥ : Ideal R) = Ideal.comap (algebraMap R K) (⊥ : Ideal K)
    apply (Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) x pt hpt
  let _ := hiso y
  let e : ↑(X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y)) ≃+* ↑((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) :=
    (asIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)).commRingCatIsoToRingEquiv
  have hxy : ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base y) = x := hy
  rw [← hxy, ringKrullDim_eq_of_ringEquiv e]
  apply hn y


-- created on 2026-10-20
