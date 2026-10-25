import Def.AlgebraicGeometry_FormalGroupAlongSection
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

namespace CerednikDrinfeld.QM


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

end
