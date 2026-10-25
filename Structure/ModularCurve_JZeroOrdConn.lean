import Structure.ModularCurve_JZeroGoodReductionV3
import Structure.ModularCurve_EichlerShimuraData
import Def.ModularCurve_JZeroOrdConn

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

namespace ModularCurve

section KernelSpan

variable {R O'' K : Type} [CommRing R] [CommRing O''] [Algebra R O''] [Field K] [Algebra O'' K]
variable {V₀ : Type} [AddCommGroup V₀] [Module R V₀]


end KernelSpan

noncomputable section OrdConn

open AlgebraicCurve IsLocalRing

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} [NeZero N]

variable [Module HeckeAlg (JZero N)]
variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]
variable (D : JZeroGoodReductionSpecialization_alt A ℓ Fact.out N)


variable (O'' : Type) [CommRing O''] [Algebra ℤ_[ℓ] O''] (K : Type) [Field K] [Algebra O'' K]
variable [Module ℤ_[ℓ] (TateModule ℓ (JZero N))]


variable {O'' K}

structure JZeroOrdConn (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) : Prop where
  finrank_inf_specKernel_le_one : Module.finrank K ↥(W ⊓ specKernel D O'' K) ≤ 1

set_option maxSynthPendingDepth 3 in


end OrdConn

end ModularCurve
