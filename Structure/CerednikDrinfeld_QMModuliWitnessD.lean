import Structure.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

structure ShimuraCurveModel.ModuliWitnessD {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) : Type 1 where

  X : Scheme.{0}

  [isIntegral : IsIntegral X]

  πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))

  smooth : Smooth πX

  proper : IsProper πX

  sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))

  sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

  pt : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
    FakeEllipticCurve Λ N S → SchemeHomOver s πX

  eF : M.F ≃+* ↥(X.functionField)

  pts : Place (AlgebraicClosure ℚ) M.Fbar ≃ SchemeHomOver sbar πX

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
    FakeEllipticCurve.Iso E E' → pt S s E = pt S s E'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1

  pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
    ∃ E : FakeEllipticCurve Λ N k, pt k s E = P

  pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
    (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E'

  pts_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) M.Fbar),
    (pts (M.gal σ • P)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts P).1

  pts_stalk : ∀ (P : Place (AlgebraicClosure ℚ) M.Fbar) (x : M.F),
    M.toBar x ∈ P.toValuationSubring ↔
      eF x ∈ (algebraMap ↥(X.presheaf.stalk ((pts P).1.base default)) ↥(X.functionField)).range

  hecke : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
        pt _ sbar E = pts P ∧ pt _ sbar E' = pts Q ∧ FakeEllipticCurve.HeckeNeighbour ℓ E E'


end CerednikDrinfeld

end
