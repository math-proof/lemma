-- Carved from Lemma/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean: instance decls only.
import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Class.AlgebraicCurve_DivisorPushPull
import Instance.DedekindDomain_AdicValuation_InlineSpecific
import Lemma.AlgebraicCurve.PlaceCompletion

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom


set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom


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

scoped instance kw_ffgc_algebraAdicCompletionComap :
    Algebra (W.restrict F).adicCompletion W.adicCompletion :=
  (kw_ffgc_adicCompletionComap F W).toAlgebra

scoped instance kw_ffgc_algebraAdicCompletionComapIntegers :
    Algebra (W.restrict F).adicCompletionIntegers W.adicCompletionIntegers :=
  (kw_ffgc_adicCompletionComapIntegers F W).toAlgebra

scoped instance kw_ffgc_algebraAdicCompletionIntegersToCompletion :
    Algebra (W.restrict F).adicCompletionIntegers W.adicCompletion :=
  ((kw_ffgc_adicCompletionComap F W).comp
    (algebraMap (W.restrict F).adicCompletionIntegers (W.restrict F).adicCompletion)).toAlgebra

instance kw_ffgc_isScalarTower_integersCompletionCompletion :
    IsScalarTower (W.restrict F).adicCompletionIntegers
      (W.restrict F).adicCompletion W.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance kw_ffgc_isScalarTower_integersIntegersCompletion :
    IsScalarTower (W.restrict F).adicCompletionIntegers
      W.adicCompletionIntegers W.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun x => (kw_ffgc_adicCompletionComapIntegers_coe F W x).symm

end CompletionAlgebra


section ClosedAdjoin

open scoped Valued NNReal WithZero

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

instance kw_ffgc_continuousSMul_adicCompletionComap :
    ContinuousSMul (W.restrict F).adicCompletion W.adicCompletion :=
  continuousSMul_of_algebraMap _ _ (by
    rw [kw_ffgc_algebraMap_adicCompletionComap_eq]
    exact kw_ffgc_continuous_adicCompletionComap F W)

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

instance kw_ffgc_finiteDimensional_adicCompletion [FiniteDimensional F F'] :
    FiniteDimensional (W.restrict F).adicCompletion W.adicCompletion := by
  letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  letI : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  let b := Module.finBasis F F'
  exact Module.Finite.of_surjective (kw_ffgc_completionLinearCombination F W b) (by
    rw [← Set.range_eq_univ, ← LinearMap.coe_range,
      ← (LinearMap.range
          (kw_ffgc_completionLinearCombination F W b)).closed_of_finiteDimensional.closure_eq]
    exact (kw_ffgc_denseRange_completionLinearCombination F W b).closure_range)

end FiniteDimensional


end AlgebraicCurve.Place

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section


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

instance instAlgebraKAdicCompletionIntegers : Algebra K u.adicCompletionIntegers :=
  (algebraMapKIntegers u).toAlgebra

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end
end
end
end
end
end
