import Def.GaloisRep_Residual
import Structure.GaloisRep_ResidualEquiv

open scoped TensorProduct

namespace ResidualGaloisRep

variable {k : Type} [Field k]


def IsEquiv (ρ₁ ρ₂ : ResidualGaloisRep k) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

def refl (ρ : ResidualGaloisRep k) : Equiv ρ ρ where
  toLinearEquiv := LinearEquiv.refl k ρ.V
  map_apply _ _ := rfl

def symm {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) : Equiv ρ₂ ρ₁ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_apply σ x := by
    apply e.toLinearEquiv.injective
    rw [e.map_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (e₁₂ : Equiv ρ₁ ρ₂) (e₂₃ : Equiv ρ₂ ρ₃) :
    Equiv ρ₁ ρ₃ where
  toLinearEquiv := e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv
  map_apply σ x := by
    rw [LinearEquiv.trans_apply, e₁₂.map_apply, e₂₃.map_apply, LinearEquiv.trans_apply]

noncomputable def baseChangeAlong {k' : Type} [Field k'] (ψ : k →+* k')
    {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChangeAlong ψ) (ρ₂.baseChangeAlong ψ) :=
  letI : Algebra k k' := ψ.toAlgebra
  { toLinearEquiv := e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange k' x) =
        (ρ₂.ρ σ).baseChange k' (e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

end Equiv

end ResidualGaloisRep
