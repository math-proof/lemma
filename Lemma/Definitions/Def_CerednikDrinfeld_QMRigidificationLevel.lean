import Lemma.Definitions.Def_CerednikDrinfeld_QMRigidification
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def IsNormLevelTransport {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ : Series (Onr ⧸ pIdeal r Onr))
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (ι : Zp2 r →+* Onr)
    (coord : ↥Λ → Zp2 r × Zp2 r)
    {n : ℕ} (P₀ : A₀.FullLevel n)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ : Rigidification r π A₀ ψ E) (Pn : E.FullLevel n) : Prop :=
  ∃ Q : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ϱ.Ab.A, Q ≫ ϱ.Ab.f = 𝟙 _ ∧
    Q ≫ ϱ.gA = Spec.map (CommRingCat.ofHom (residueLeg π ψ)) ≫ (P₀.P).1 ∧
    ∃ (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (_ : E.IsFormalModuleVia coord X θ)
      (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
      IsRigTransport θ₀ κ β₀ ϱ θ j t ∧
      t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ≫ (nsmulPt E.L (𝟙 _) (r ^ t.n) Pn.P).1 =
        Q ≫ ϱ.φ' ≫ ϱ.gb

end CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification
