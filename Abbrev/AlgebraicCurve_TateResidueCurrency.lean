import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Class.AlgebraicCurve_DivisorPushPull
import Class.ModularCurve_CanonicalDivisor
import Lemma.Scheme.CanonicalDivisorUniformizer
import Class.AlgebraicCurve_CanonicalDivisor
import Structure.AlgebraicCurve_AdelicIndex
import Class.AlgebraicCurve_LocalResidue
import Instance.DedekindDomain_AdicValuation_InlineSpecific
import Instance.AlgebraicCurve_PlaceCompletion

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open LinearMap Submodule

noncomputable section

namespace ModularCurve.KwF4gRRTate

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false
set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]


end CorrectedCarrier

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

abbrev kaehlerCotrace : Ω[E⁄K] →ₗ[E] Ω[F⁄K] :=
  KaehlerDifferential.map K K E F


end KaehlerCotrace

end AlgebraicCurve

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end CompletionTraceSumMint

end AlgebraicCurve

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

end TateAtoms

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place FunctionField KaehlerDifferential

noncomputable section

namespace ModularCurve.KwF4R1V391a

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Mint

end ModularCurve.KwF4R1V391a

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end KCurrencyRow

end AlgebraicCurve

end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace AlgebraicCurve

open scoped Polynomial

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end KCurrencyRowA

end AlgebraicCurve

end
