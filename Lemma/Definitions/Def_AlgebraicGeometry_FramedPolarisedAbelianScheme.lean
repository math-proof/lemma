import Lemma.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Scheme.Modules

def IsSectionBasisOn {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    (V : X.Opens) {m : ℕ} (σ : Fin m → Γ(M, V)) : Prop :=
  Function.Bijective fun c : Fin m → S =>
    ∑ i, ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • σ i

abbrev IsSectionBasis {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {m : ℕ} (σ : Fin m → Γ(M, ⊤)) : Prop :=
  IsSectionBasisOn f M ⊤ σ

end Scheme.Modules

structure FramedPolarisedAbelianScheme (g N n : ℕ) (S : Type u) [CommRing S]
    extends PolarisedAbelianScheme g (N + 1) n S where

  frame : Scheme.Modules.ProjPresentation pol f N

  frame_isClosedImmersion : IsClosedImmersion frame.toProj

  frame_basis : Scheme.Modules.IsSectionBasis f pol frame.σ

namespace FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def Iso {S : Type u} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ (e : X.A ≅ X'.A) (he : e.hom ≫ X'.f = X.f),
    e.hom ≫ X'.frame.toProj = X.frame.toProj ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (X.P i).1 ≫ e.hom = (X'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj X'.pol) ≅
        (Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj X.pol))

def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') : Prop :=
  letI : Algebra S S' := φ.toAlgebra
  ∃ (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
      (X'.L.mul t' x y).1 ≫ gA =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
    X'.frame.toProj ≫ ProjSpace.map S S' N = gA ≫ X.frame.toProj

structure IsFineModuli (g N n : ℕ) {B : Type} [CommRing B]
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : FramedPolarisedAbelianScheme g N n S), Iso X X' → pt S s X = pt S s X'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
    IsPullback φ X X' → (pt S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s X).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πH),
    ∃ X : FramedPolarisedAbelianScheme g N n S, pt S s X = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : FramedPolarisedAbelianScheme g N n S), pt S s X = pt S s X' → Iso X X'

end FramedPolarisedAbelianScheme

end AlgebraicGeometry

end
