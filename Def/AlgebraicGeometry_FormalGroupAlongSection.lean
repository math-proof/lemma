import Class.MvFormalGroup_BasicV2
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Def.CerednikDrinfeld_SchemeNilpPoints
import Abbrev.AlgebraicGeometry_FormalGroupAlongSection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace MvFormalGroup

variable {B : Type} [CommRing B]

def nilEval {σ : Type} [Fintype σ] [DecidableEq σ] {B' : Type} [CommRing B'] [Algebra B B']
    (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') : B' :=
  MvPolynomial.aeval a (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ)

def nilMul {g : ℕ} (F : MvFormalGroup g B) {B' : Type} [CommRing B'] [Algebra B B'] (n : ℕ)
    (s t : Fin g → B') : Fin g → B' :=
  fun i => nilEval n (F.toPowerSeries i) (Sum.elim s t)

end MvFormalGroup

namespace GoodReductionJacobian.RelativeGroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

def IsInfinitesimal (L : RelativeGroupLaw B f) {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B')
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) : Prop :=
  schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) P =
    L.one (Scheme.specOver (𝒪 := B) (B' ⧸ J))

def IsFormalCoordinates (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) (θ : FormalCoordinates f g) : Prop :=

    (∀ (B' : Type) [CommRing B'] [Algebra B B'] (B'' : Type) [CommRing B''] [Algebra B B''] (φ : B' →ₐ[B] B'')
        (s : Fin g → B'), (∀ i, IsNilpotent (s i)) →
        θ B'' (φ ∘ s) = schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (Scheme.specMap_algHom_comp_specOver φ) (θ B' s)) ∧

    (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
        (∀ s : Fin g → B', (∀ i, s i ∈ J) → L.IsInfinitesimal J (θ B' s)) ∧
        (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) → θ B' s = θ B' t → s = t) ∧
        (∀ P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f, L.IsInfinitesimal J P →
          ∃ s : Fin g → B', (∀ i, s i ∈ J) ∧ θ B' s = P) ∧
        (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) →
          θ B' (F.nilMul n s t) = L.mul (Scheme.specOver (𝒪 := B) B') (θ B' s) (θ B' t)))

def IsFormalGroupAlong (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) : Prop :=
  ∃ θ : FormalCoordinates f g, L.IsFormalCoordinates F θ

end GoodReductionJacobian.RelativeGroupLaw
