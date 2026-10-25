import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Trace
import Structure.JacJ1Iface
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Instance.CerednikDrinfeld_ShimuraCurve

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

section Points

variable {R : Type u} [CommRing R]

def mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩


def FactorsThrough {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (lev : C ⟶ A)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : Prop :=
  ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1

def nsmulPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : ℕ → SchemeHomOver t f → SchemeHomOver t f
  | 0, _ => L.one t
  | n + 1, P => L.mul t (nsmulPt L t n P) P

end Points

section Tangent

variable {S : Type u} [CommRing S]

def geomPoint (k : Type u) [Field k] (sk : S →+* k) : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom sk)

def tangentBase (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp sk))

def tangentZero (k : Type u) [Field k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

def tangentScale (k : Type u) [Field k] (c : k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)

def IsTangentVector {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (k : Type u) [Field k] (sk : S →+* k) (P : SchemeHomOver (tangentBase k sk) f) : Prop :=
  tangentZero k ≫ P.1 = (L.one (geomPoint k sk)).1

end Tangent

variable {a b : ℚ}

structure FakeEllipticCurve (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (S : Type u) [CommRing S] : Type (u + 1) where

  A : Scheme.{u}

  f : A ⟶ Spec (CommRingCat.of S)

  L : RelativeGroupLaw S f

  comm : L.IsCommutative

  bundle : AbelianSchemePropertyBundle S f

  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2

  act : ↥Λ → (A ⟶ A)

  act_over : ∀ x : ↥Λ, act x ≫ f = f

  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)

  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A

  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x

  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

  act_trace : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
    (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
    ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
    ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k V Φ = (n : k)

  C : Scheme.{u}

  lev : C ⟶ A

  lev_closed : IsClosedImmersion lev

  lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P)

  lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough lev (L.one t)

  lev_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → nsmulPt L t N P = L.one t

  lev_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → FactorsThrough lev (pushPt (act x) (act_over x) P)

  lev_finite : IsFinite (lev ≫ f)

  lev_flat : Flat (lev ≫ f)

  lev_finitePresentation : LocallyOfFinitePresentation (lev ≫ f)

  lev_rank : ∀ s : ↥(Spec (CommRingCat.of S)), (lev ≫ f).finrank s = N ^ 2

  lev_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
    ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
      ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)

namespace FakeEllipticCurve

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def Iso {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P))

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') : Prop :=
  ∃ (g : E'.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      FactorsThrough E'.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)

def HeckeNeighbour {S : Type u} [CommRing S] (ℓ : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      FactorsThrough E'.lev P → FactorsThrough E.lev (mapPt ψ hψ P)) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E'.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    ¬ IsIso φ ∧ ¬ IsIso ψ

end FakeEllipticCurve

end CerednikDrinfeld.QM

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

structure ShimuraCurveModel.ModuliWitness {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' : ℕ) : Type 1 where

  X : Scheme.{0}

  [isIntegral : IsIntegral X]

  πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))

  smooth : Smooth πX

  proper : IsProper πX

  sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))

  sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((N * q * q' : ℕ) : ℤ)))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

  pt : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))),
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
