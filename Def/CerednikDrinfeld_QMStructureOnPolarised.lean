import Def.CerednikDrinfeld_QMCanonicalPol
import Structure.CerednikDrinfeld_QMStructureOnPolarised

set_option autoImplicit false

noncomputable section

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

namespace AlgebraicGeometry.PolarisedAbelianScheme

variable {a b : ℚ}


namespace QMStructure

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}

def IsPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X') : Prop :=
  ∃ (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
      (X'.L.mul t' x y).1 ≫ gA =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
    (∀ x : ↥Λ, s'.act x ≫ gA = gA ≫ s.act x) ∧
    s'.P.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ s.P.1

def Iso {S : Type} [CommRing S] {X X' : PolarisedAbelianScheme 2 d m S}
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X') : Prop :=
  ∃ (e : X.A ≅ X'.A) (he : e.hom ≫ X'.f = X.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (X.P i).1 ≫ e.hom = (X'.P i).1) ∧
    (∀ p : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj X'.pol) ≅
        (Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj X.pol)) ∧
    (∀ x : ↥Λ, s.act x ≫ e.hom = e.hom ≫ s'.act x) ∧
    s.P.1 ≫ e.hom = s'.P.1

def Packages {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S}
    (s : QMStructure Λ star β X) (u : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 m S) : Prop :=
  ∃ (e : u.1.A ≅ X.A) (he : e.hom ≫ X.f = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.1.f),
      (u.1.L.mul t x y).1 ≫ e.hom =
        (X.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ s.act x) ∧
    u.2.P.1 ≫ e.hom = s.P.1

end QMStructure

end AlgebraicGeometry.PolarisedAbelianScheme

end
