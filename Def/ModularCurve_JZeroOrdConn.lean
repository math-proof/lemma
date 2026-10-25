import Structure.ModularCurve_JZeroGoodReductionV3
import Def.ModularCurve_EichlerShimuraData

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

namespace ModularCurve


noncomputable section OrdConn

open AlgebraicCurve IsLocalRing

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} [NeZero N]

variable [Module HeckeAlg (JZero N)]
variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]
variable (D : JZeroGoodReductionSpecialization_alt A ℓ Fact.out N)

def specKernelSet : Set (TateModule ℓ (JZero N)) :=
  {x | ∀ n : ℕ, D.sp ((x : ℕ → JZero N) n) = 0}

variable (O'' : Type) [CommRing O''] [Algebra ℤ_[ℓ] O''] (K : Type) [Field K] [Algebra O'' K]
variable [Module ℤ_[ℓ] (TateModule ℓ (JZero N))]

def specKernel : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N))) :=
  Submodule.span K (Set.range fun p : O'' × specKernelSet D =>
    (1 : K) ⊗ₜ[O''] (p.1 ⊗ₜ[ℤ_[ℓ]] (p.2 : TateModule ℓ (JZero N))))

end OrdConn

end ModularCurve
