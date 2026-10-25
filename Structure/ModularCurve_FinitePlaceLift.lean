import Lemma.WeierstrassCurve.ReductionMap
import Structure.AlgebraicCurve_ConstantReduction
import Def.AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section NuBall

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)


end NuBall

structure FinitePlaceLift (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (ν : NumberField.FinitePlace ↥L) : Type where

  A : ValuationSubring (AlgebraicClosure ℚ)

  mem_iff : ∀ a : ↥L, (↑a : AlgebraicClosure ℚ) ∈ A ↔ ν a ≤ 1

  p : ℕ

  pprime : p.Prime

  lies : A.LiesOverPrime p

namespace FinitePlaceLift

variable {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
  {ν : NumberField.FinitePlace ↥L} (M : FinitePlaceLift L ν)


end FinitePlaceLift

section Existence

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)


end Existence


end ModularCurve

namespace AlgebraicCurve

open IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

namespace ConstantReduction


section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]


end DegenerateMember

end ConstantReduction

end AlgebraicCurve
