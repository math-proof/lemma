import Lemma.Definitions.Def_ModularCurve_ResidualRealization
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois
import Lemma.Definitions.Def_FLTPrelim_ModularRep

set_option autoImplicit false

open Module LinearMap CongruenceSubgroup
open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

namespace FreyPackage

def ESMasterAttachmentSupplyField (P : FreyPackage) (M : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J] : Prop :=
  ∀ (g : CuspForm (Gamma0 M) 2), g.IsNormalizedEigenform →
    ∀ (𝔪 : Ideal (integralClosure ℤ ℂ)), 𝔪.IsMaximal → (P.p : integralClosure ℤ ℂ) ∈ 𝔪 →
      ∃ (k : Type) (_ : Field k) (φ : HeckeAlg →+* k)
        (V : Type) (_ : AddCommGroup V) (_ : Module k V)
        (π : J → V)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V))
        (ψ : integralClosure ℤ ℂ →+* k)
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        ((P.p : k) = 0) ∧
        IsResidualRealization P.p J k φ V π ρ ∧
        CyclotomicDeterminant M P.p ρ ∧
        𝔪 ≤ RingHom.ker ψ ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * P.p → ∃ a : integralClosure ℤ ℂ,
          (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧ φ (heckeGen ⟨ℓ, hℓ⟩) = ψ a) ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p).ker ⊓
            ρ.ker

def EigenformRealizationSupplyFieldAt (P : FreyPackage) (M : ℕ)
    [Module HeckeAlg (JZero M)] : Prop :=
  ESMasterAttachmentSupplyField P M (JZero M)

theorem eigenformRealizationSupplyFieldAt_iff_eSMasterAttachmentSupplyField
    {P : FreyPackage} {M : ℕ} [Module HeckeAlg (JZero M)] :
    P.EigenformRealizationSupplyFieldAt M ↔ ESMasterAttachmentSupplyField P M (JZero M) :=
  Iff.rfl

end FreyPackage
