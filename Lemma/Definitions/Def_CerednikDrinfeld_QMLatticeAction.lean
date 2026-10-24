import Lemma.Definitions.Def_CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

variable {a b : ℚ}

structure LatticeAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type u} [CommRing S] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) : Type u where

  act : ↥Λ → (A ⟶ A)

  act_over : ∀ x : ↥Λ, act x ≫ f = f

  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)

  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A

  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x

  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

namespace LatticeAction

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]}

@[ext] theorem ext {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {X Y : LatticeAction Λ f L} (h : X.act = Y.act) : X = Y := by
  cases X; cases Y; cases h; rfl

def ofFakeEllipticCurve {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) : LatticeAction Λ E.f E.L where
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add

@[simp] theorem ofFakeEllipticCurve_act {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    (ofFakeEllipticCurve E).act = E.act := rfl

end LatticeAction

def IsGroupPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f') (g : A' ⟶ A) : Prop :=
  ∃ hg : CategoryTheory.IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)),
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

structure RepresentsLatticeActions (Λ : Submodule ℤ ℍ[ℚ, a, b]) {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (E : Scheme.{u}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A), IsGroupPullback φ L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE) : Prop where

  cl_comp : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L')
      (R'' : Type u) [CommRing R''] (ψ : R' →+* R'') {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
      (L'' : RelativeGroupLaw R'' f'') (g'' : A'' ⟶ A) (hg'' : IsGroupPullback (ψ.comp φ) L L'' g'')
      (X'' : LatticeAction Λ f'' L'') (h : A'' ⟶ A'),
      IsGroupPullback ψ L' L'' h → h ≫ g = g'' → (∀ x : ↥Λ, X''.act x ≫ h = h ≫ X'.act x) →
      (cl R'' (ψ.comp φ) L'' g'' hg'' X'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (cl R' φ L' g hg X').1

  cl_surjective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g)
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE), ∃ X' : LatticeAction Λ f' L', cl R' φ L' g hg X' = s

  cl_injective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X₁ X₂ : LatticeAction Λ f' L'),
      cl R' φ L' g hg X₁ = cl R' φ L' g hg X₂ → X₁ = X₂

end CerednikDrinfeld.QM

end
