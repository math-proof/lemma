import Mathlib
import Structure.AlgebraicCurve_LocalResidue

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (v : Place K F)

structure CoefficientFieldSection where

  lift : v.ResidueField →ₐ[K] v.toValuationSubring

  residue_lift : ∀ a, IsLocalRing.residue _ (lift a) = a

structure CanonicalLocalResidueDataS (σ : v.CoefficientFieldSection)
    extends v.LocalResidueData where

  res_higherPoleSectionMonomial : ∀ (n : ℕ), 1 ≤ n → ∀ a : v.ResidueField,
    res ((σ.lift a : F) * (v.uniformizer ^ (n + 1))⁻¹) = 0

end Place

end AlgebraicCurve

namespace ModularCurve.Lg37

open AlgebraicCurve

section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev lg37_completion (v : Place K F) : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal v.toValuationSubring) v.toValuationSubring

def lg37_residueHat (v : Place K F) :
    lg37_completion v →+* v.ResidueField :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal v.toValuationSubring)).toRingHom

structure Lg37CompletionSection (v : Place K F) where

  lift : v.ResidueField →ₐ[K] lg37_completion v

  residueHat_lift : ∀ a, lg37_residueHat v (lift a) = a

end CompletionCarrier

end ModularCurve.Lg37
