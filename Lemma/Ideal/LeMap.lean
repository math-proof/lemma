import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma g3c_map_le_map_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) (a b : Ideal R) : a.map φ ≤ b.map φ ↔ a ≤ b := by
  refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
  have := Ideal.comap_mono (f := φ) h
  rwa [Ideal.comap_map_of_bijective φ hφ, Ideal.comap_map_of_bijective φ hφ] at this
/--
[AlgebraicGeometry_Spec_map_germ_le_iff_map_algebraMap_localization_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Spec_map_germ_le_iff_map_algebraMap_localization_le.lean)
-/
@[path]
private lemma main
    (A : Type u) [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (J K : Ideal ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤))) :
    Ideal.map ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) trivial).hom J ≤
        Ideal.map ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) trivial).hom K ↔
      Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) J ≤
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) K := by
  set x : PrimeSpectrum A := ⟨𝔭, inferInstance⟩ with hx
  let S : Type u := (Spec (CommRingCat.of A)).presheaf.stalk x
  let instAlg : Algebra A S := StructureSheaf.stalkAlgebra (R := A) x
  let _ : IsLocalization.AtPrime S 𝔭 := StructureSheaf.IsLocalization.to_stalk A x
  let θ : S ≃ₐ[A] Localization.AtPrime 𝔭 := IsLocalization.algEquiv 𝔭.primeCompl S (Localization.AtPrime 𝔭)
  let instΓ : Algebra A ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤)) :=
    StructureSheaf.openAlgebra (R := A) (Opposite.op ⊤)
  let γ : ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤)) →+* S := ((Spec (CommRingCat.of A)).presheaf.germ ⊤ x trivial).hom
  have hγ : ∀ a : A, γ (algebraMap A _ a) = algebraMap A S a := by
    intro a
    have h := StructureSheaf.algebraMap_germ (R := A) ⊤ x trivial
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) h
    exact this
  have hinv : ∀ s : (Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) = s := fun s =>
    congrArg (fun φ => (CommRingCat.Hom.hom φ) s) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  have hcomp : (θ : S →+* Localization.AtPrime 𝔭).comp
        ((Spec (CommRingCat.of A)).presheaf.germ ⊤ x trivial).hom =
      (algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom := by
    apply RingHom.ext
    intro s
    show θ (γ s) = algebraMap A (Localization.AtPrime 𝔭) ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s)
    have e : ∀ a : A, (algebraMap A ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤)) a) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a := fun a => rfl
    have h2 : γ s = algebraMap A S ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) := by
      rw [← hγ, e, hinv]
    rw [h2]
    exact θ.commutes _
  have hθ : Function.Bijective (θ : S →+* Localization.AtPrime 𝔭) := θ.bijective
  have e1 : ∀ L : Ideal ((Spec (CommRingCat.of A)).presheaf.obj (Opposite.op ⊤)),
      Ideal.map (θ : S →+* Localization.AtPrime 𝔭) (Ideal.map ((Spec (CommRingCat.of A)).presheaf.germ ⊤ x trivial).hom L) =
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) L := by
    intro L
    rw [← hcomp]
    exact Ideal.map_map _ _
  refine (g3c_map_le_map_iff_of_bijective (θ : S →+* Localization.AtPrime 𝔭) hθ _ _).symm.trans ?_
  rw [e1, e1]

-- created on 2026-10-20
