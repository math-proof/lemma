import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {S : Type u} [CommRing S] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of S))
private lemma of_affine {V : Scheme.{u}} [IsAffine V] (ι : V ⟶ H) [Mono ι]
    (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S''), Function.Surjective ψ →
      RingHom.ker ψ ^ 2 = ⊥ →
      ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H),
        x₁ ≫ q = s → x₂ ≫ q = s →
        Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
    FormallyUnramified (ι ≫ q) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)]
  let φ := (ι ≫ q).appTop
  let _ : Algebra Γ(Spec (CommRingCat.of S), ⊤) Γ(V, ⊤) := φ.hom.toAlgebra
  show Algebra.FormallyUnramified Γ(Spec (CommRingCat.of S), ⊤) Γ(V, ⊤)
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B' _ _ I hI a₁ a₂ ha
  let x : (Γ(V, ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] B') → (Spec (CommRingCat.of B') ⟶ H) :=
    fun a => Spec.map (CommRingCat.ofHom a.toRingHom) ≫ V.isoSpec.inv ≫ ι
  let s : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Spec (CommRingCat.of S), ⊤) B')) ≫ (Spec (CommRingCat.of S)).isoSpec.inv
  have hx : ∀ a : Γ(V, ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] B', x a ≫ q = s := by
    intro a
    simp only [x, s, Category.assoc]
    rw [← Scheme.isoSpec_inv_naturality (ι ≫ q), ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    change a.toRingHom (φ.hom r) = algebraMap _ B' r
    exact a.commutes r
  have hψ : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥ := by rw [Ideal.mk_ker, hI]
  have hagree : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x a₁ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x a₂ := by
    simp only [x, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext r
    change Ideal.Quotient.mk I (a₁ r) = Ideal.Quotient.mk I (a₂ r)
    exact congrArg (fun h : Γ(V, ⊤) →ₐ[Γ(Spec (CommRingCat.of S), ⊤)] B' ⧸ I => h r) ha
  have hxx : x a₁ = x a₂ :=
    huniq B' (B' ⧸ I) (Ideal.Quotient.mk I) hψ hker s (x a₁) (x a₂) (hx a₁) (hx a₂) hagree
  have h2 : Spec.map (CommRingCat.ofHom a₁.toRingHom) = Spec.map (CommRingCat.ofHom a₂.toRingHom) := by
    simpa only [x, cancel_mono] using hxx
  have h3 := Spec.map_injective h2
  apply AlgHom.ext
  intro r
  exact congrArg (fun h : CommRingCat.of Γ(V, ⊤) ⟶ CommRingCat.of B' => h.hom r) h3
/--
[AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq.lean)
-/
@[path]
private lemma main
    {S : Type u} [CommRing S] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of S))
    (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S''), Function.Surjective ψ →
      RingHom.ker ψ ^ 2 = ⊥ →
      ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H),
        x₁ ≫ q = s → x₂ ≫ q = s →
        Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
    FormallyUnramified q := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) H.affineCover]
  intro i
  exact of_affine q (H.affineCover.f i) huniq

-- created on 2026-10-20
