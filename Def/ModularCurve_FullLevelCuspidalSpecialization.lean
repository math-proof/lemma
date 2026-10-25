import Instance.ModularCurve_FullLevelJacobian
import Lemma.Matrix.TateProdRep.eq.TateRep

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve.FullLevel

section Coord

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

def ratCoord (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (ζ : Idx q) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M') :=
  ((LinearMap.proj ζ : (Idx q → TateModule lam (jacComp q M')) →ₗ[ℤ_[lam]] TateModule lam (jacComp q M')) ∘ₗ
      Ψ.toLinearMap).baseChange ℚ_[lam]

end Coord

section Specialization

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (k : Type) [Field k] [IsDomain (DrinfeldCurve.CoordRing q k)]

def componentSpecialization
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] DrinfeldCurve.tateProd q k lam ℚ_[lam] (Idx q × T) :=
  LinearMap.pi fun p =>
    TensorProduct.mk ℚ_[lam] ℚ_[lam]
        (RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) 1 ∘ₗ
      Φ p.1 p.2 ∘ₗ LinearMap.proj (c p.2) ∘ₗ red ∘ₗ eInv ∘ₗ ratCoord q M' lam Ψ p.1

def cuspidalSpecialization
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] DrinfeldCurve.tateProd q k lam ℚ_[lam] (Idx q × T) :=
  componentSpecialization q M' lam k Ψ Vinv eInv red c Φ ∘ₗ eC

end Specialization

end ModularCurve.FullLevel

end
