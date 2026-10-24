import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

structure ExtraLevel (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) : Type (u + 1) where

  K : Scheme.{u}

  levK : K ⟶ E.A

  levK_closed : IsClosedImmersion levK

  levK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK Q → FactorsThrough levK (E.L.mul t P Q) ∧ FactorsThrough levK (E.L.inv t P)

  levK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough levK (E.L.one t)

  levK_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → nsmulPt E.L t ℓ P = E.L.one t

  levK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK (pushPt (E.act x) (E.act_over x) P)

  levK_disjoint : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough E.lev P → P = E.L.one t

  levK_finite : IsFinite (levK ≫ E.f)

  levK_flat : Flat (levK ≫ E.f)

  levK_finitePresentation : LocallyOfFinitePresentation (levK ≫ E.f)

  levK_rank : ∀ s : ↥(Spec (CommRingCat.of S)), (levK ≫ E.f).finrank s = ℓ ^ 2

  levK_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (ℓ : k) ≠ 0 →
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)

abbrev WithExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.ExtraLevel ℓ

def WithExtraLevel.Iso {ℓ : ℕ} (u u' : WithExtraLevel Λ N ℓ S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔ FactorsThrough u'.2.levK (mapPt e.hom he P))

def IsLevelRestrict {ℓ : ℕ} (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) : Prop :=
  FakeEllipticCurve.Iso u.1 d

def IsLevelIsogeny (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧ (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough u.2.levK P) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough d.lev (mapPt φ hφ P))

def IsAtkinLehnerQuotient (r : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E'.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

def WithExtraLevel.IsAtkinLehnerQuotient {ℓ : ℕ} (r : ℕ) (u u' : WithExtraLevel Λ N ℓ S) : Prop :=
  ∃ (φ : u.1.A ⟶ u'.1.A) (hφ : φ ≫ u'.1.f = u.1.f) (ψ : u'.1.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = u'.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u'.1.f),
      mapPt ψ hψ (u'.1.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ u'.1.act x) ∧ (∀ x : ↥Λ, u'.1.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = u'.1.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = u'.1.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (u.1.act m) (u.1.act_over m) P = u.1.L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough u'.1.lev (mapPt φ hφ P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P → FactorsThrough u'.2.levK (mapPt φ hφ P))

end CerednikDrinfeld.QM.FakeEllipticCurve

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

def ShimuraCurveModel.ModuliWitness.IsOriented {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ}
    (w : M.ModuliWitness Λ N q q') : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        w.pt _ w.sbar u.1 = w.pts P ∧ w.pt _ w.sbar d = w.pts Q ∧ FakeEllipticCurve.IsLevelIsogeny ℓ u d

def ShimuraCurveModel.ModuliWitness.IsGoodReductionModel {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ}
    (w : M.ModuliWitness Λ N q q') : Prop :=
  SmoothOfRelativeDimension 1 w.πX ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))),
    IsIntegral (CategoryTheory.Limits.pullback w.πX s)

end CerednikDrinfeld

end
