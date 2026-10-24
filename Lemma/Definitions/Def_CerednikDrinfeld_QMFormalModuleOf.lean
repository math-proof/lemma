import Lemma.Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

namespace CerednikDrinfeld.QM

structure IsOrderCoord {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) [Fact q.Prime] (coord : ↥Λ → Zp2 q × Zp2 q) : Prop where
  map_add : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m'
  map_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, coord ⟨1, h⟩ = (1, 0)
  map_mul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
    coord ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ =
      ((coord m).1 * (coord m').1 + (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m').2),
        (coord m).1 * (coord m').2 + (coord m).2 * WittVector.frobenius (coord m').1)
  injective : Function.Injective coord
  dense : ∀ (k : ℕ) (α β : Zp2 q), ∃ m : ↥Λ,
    (coord m).1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k}
  trace : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
    (coord m).1 + WittVector.frobenius (coord m).1 = (n : Zp2 q)

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]

def IsPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A) : Prop :=
  ∃ (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) ∧
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      FactorsThrough E'.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)

def IsFormalModuleVia (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) : Prop :=
  E.L.IsFormalCoordinates X.F θ ∧
    ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ (m : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n
            (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) s) =
          pushPt (E.act m) (E.act_over m) (θ B' s)

def IsFormalModuleOf (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B) : Prop :=
  ∃ θ : RelativeGroupLaw.FormalCoordinates E.f 2, E.IsFormalModuleVia coord X θ

end FakeEllipticCurve

end CerednikDrinfeld.QM
