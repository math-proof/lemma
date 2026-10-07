import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S]
  {K : Scheme.{u}}
  {p : K ⟶ Spec (CommRingCat.of S)} [IsFinite p] [Flat p]
  {𝒢 : K.Opens}
-- given
  (h𝒢 : IsClosed (𝒢 : Set ↥K)) :
-- imply
  ∃ (S' : Type u) (_ : CommRing S') (φ : S →+* S') (e : Spec (CommRingCat.of S') ≅ (𝒢 : Scheme.{u})),
      e.hom ≫ 𝒢.ι ≫ p = Spec.map (CommRingCat.ofHom φ) ∧
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      (Surjective (𝒢.ι ≫ p) → Surjective (Spec.map (CommRingCat.ofHom φ))) := by
-- proof
  classical
  have : IsAffineHom p := inferInstance
  have : IsAffine K := isAffine_of_isAffineHom p

  have : IsClosedImmersion 𝒢.ι := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [Scheme.Opens.range_ι]; exact h𝒢
  have : IsAffine (𝒢 : Scheme.{u}) := isAffine_of_isAffineHom 𝒢.ι
  let G : Scheme.{u} := 𝒢
  let e : Spec Γ(G, ⊤) ≅ G := G.isoSpec.symm
  let f : Spec Γ(G, ⊤) ⟶ Spec (CommRingCat.of S) := e.hom ≫ 𝒢.ι ≫ p
  let φ : S →+* Γ(G, ⊤) := (Spec.preimage f).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = f := by
    simp only [φ, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨Γ(G, ⊤), inferInstance, φ, e, hφ.symm, ?_, ?_⟩
  · rw [hφ]; infer_instance
  · intro hs; rw [hφ]; have := hs; infer_instance


-- created on 2026-10-05
