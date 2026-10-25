import Mathlib.RepresentationTheory.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Def.FLTPrelim_ModularRep
import Lemma.FLTPrelim.FreyPackage
import Instance.EllipticCurve_FrobeniusTrace

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarCongruenceRecovery :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def EigenformResidualAttachmentAt (P : FreyPackage) (M : ℕ) : Prop :=
  ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNormalizedEigenform →
    ∀ (𝔪 : Ideal (integralClosure ℤ ℂ)), 𝔪.IsMaximal → (P.p : integralClosure ℤ ℂ) ∈ 𝔪 →
      ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod P.p) K)
        (V : Type) (_ : AddCommGroup V) (_ : Module K V)
        (ρ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
        (ψ : integralClosure ℤ ℂ →+* K)
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        𝔪 ≤ RingHom.ker ψ ∧
        Module.finrank K V = 2 ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p).ker ⊓
            ρ.ker ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
                LinearMap.trace K V (ρ τ) = ψ a) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              LinearMap.det (ρ τ) = (ℓ : K))

end FreyPackage
