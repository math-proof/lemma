import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Class.AlgebraicCurve_DivisorPushPull
import Instance.DedekindDomain_AdicValuation_InlineSpecific

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

namespace AlgebraicCurve.Place

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

abbrev adicCompletion : Type _ := V.heightOneSpectrum.adicCompletion F

abbrev adicCompletionIntegers : ValuationSubring V.adicCompletion :=
  V.heightOneSpectrum.adicCompletionIntegers F

end AdicCompletion

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

end AlgebraicCurve.Place

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom

namespace AlgebraicCurve.Place

section IntegerComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end IntegerComap

end AlgebraicCurve.Place

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open Polynomial IsLocalRing IsDedekindDomain

namespace AlgebraicCurve.Place

section CompletionAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionAlgebra

section SpectralSetup

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end SpectralSetup

section AbsoluteValue

open scoped Valued NNReal WithZero

open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end AbsoluteValue

section ClosedAdjoin

open scoped Valued NNReal WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end ClosedAdjoin

end AlgebraicCurve.Place

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

open scoped Valued WithZero

namespace AlgebraicCurve.Place

section FiniteDimensional

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end FiniteDimensional

section CompletionTrace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

abbrev kw_ffgc_completionTrace [FiniteDimensional F F'] :
    W.adicCompletion →ₗ[(W.restrict F).adicCompletion] (W.restrict F).adicCompletion :=
  Algebra.trace (W.restrict F).adicCompletion W.adicCompletion

end CompletionTrace

end AlgebraicCurve.Place

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section

namespace AlgebraicCurve

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

namespace Place

end Place

end LocalResidueCompletion

end AlgebraicCurve

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

noncomputable section

namespace ModularCurve.KwF4gRRTate

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end
