import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma of_affine
  {S : Type u} [CommRing S]
  {H : (Scheme : Type (u + 1))}
  (q : H ⟶ Spec (CommRingCat.of S))
  {V : (Scheme : Type (u + 1))} [IsAffine V]
  (ι : V ⟶ H) [Mono ι]
    (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : RingHom S' S''), Function.Surjective ψ → RingHom.ker ψ ^ 2 = ⊥ → ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H), x₁ ≫ q = s → x₂ ≫ q = s → Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
    FormallyUnramified (ι ≫ q) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)]
  let φ := (ι ≫ q).appTop
  let _ : Algebra ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) (V.presheaf.obj (op ⊤)) := φ.hom.toAlgebra
  show Algebra.FormallyUnramified ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) (V.presheaf.obj (op ⊤))
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B' _ _ I hI a₁ a₂ ha
  let x : ((AlgHom ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) (V.presheaf.obj (op ⊤)) B')) → (Spec (CommRingCat.of B') ⟶ H) :=
    fun a => Spec.map (CommRingCat.ofHom a.toRingHom) ≫ V.isoSpec.inv ≫ ι
  let s : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) B')) ≫ (Spec (CommRingCat.of S)).isoSpec.inv
  have hx : ∀ a : (AlgHom ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) (V.presheaf.obj (op ⊤)) B'), x a ≫ q = s := by
    intro a
    simp only [x, s, Category.assoc]
    rw [← Scheme.isoSpec_inv_naturality (ι ≫ q), ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    change a.toRingHom (φ.hom r) = algebraMap _ B' r
    apply a.commutes
  have hψ : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥ := by rw [Ideal.mk_ker, hI]
  have hagree : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x a₁ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x a₂ := by
    simp only [x, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext r
    change Ideal.Quotient.mk I (a₁ r) = Ideal.Quotient.mk I (a₂ r)
    apply congrArg (fun h : AlgHom ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) (V.presheaf.obj (op ⊤)) (B' ⧸ I) => h r) ha
  have hxx : x a₁ = x a₂ :=
    huniq B' (B' ⧸ I) (Ideal.Quotient.mk I) hψ hker s (x a₁) (x a₂) (hx a₁) (hx a₂) hagree
  have h2 : Spec.map (CommRingCat.ofHom a₁.toRingHom) = Spec.map (CommRingCat.ofHom a₂.toRingHom) := by
    simpa only [x, cancel_mono] using hxx
  have h3 := Spec.map_injective h2
  apply AlgHom.ext
  intro r
  apply congrArg (fun h : CommRingCat.of (V.presheaf.obj (op ⊤)) ⟶ CommRingCat.of B' => h.hom r) h3

/--
[AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {H : (Scheme : Type (u + 1))} (q : H ⟶ Spec (CommRingCat.of S))
  (huniq : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : RingHom S' S''), Function.Surjective ψ → RingHom.ker ψ ^ 2 = ⊥ → ∀ (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x₁ x₂ : Spec (CommRingCat.of S') ⟶ H), x₁ ≫ q = s → x₂ ≫ q = s → Spec.map (CommRingCat.ofHom ψ) ≫ x₁ = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ → x₁ = x₂) :
  FormallyUnramified q := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) H.affineCover]
  intro i
  apply of_affine q (H.affineCover.f i) huniq


-- created on 2026-10-20
