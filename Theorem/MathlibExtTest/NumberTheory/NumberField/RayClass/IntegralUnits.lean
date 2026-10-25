/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/IntegralUnits.lean -/

import Theorem.NumberTheory.NumberField.RayClass.IntegralUnits.Part4
import Lemma.Nat.NumberField.RayClass.IntegralUnits
@[expose] public noncomputable section

open NumberField
open NumberField.Modulus


namespace IntegralUnitsTest

variable {K : Type*} [Field K] [NumberField K]

-- Field-unit coercion of the ray-element image.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
      integralUnitsToFieldUnits u :=
  integralUnitsToRayElements_coe m u

-- Identity maps to the identity ray element.
example (m : Modulus K) :
    integralUnitsToRayElements m 1 = 1 := by
  simp

-- Injectivity of the integral-unit maps.
example (m : Modulus K) :
    Function.Injective (integralUnitsToRayElements m) :=
  integralUnitsToRayElements_injective m

example :
    Function.Injective (integralUnitsToFieldUnits (K := K)) :=
  integralUnitsToFieldUnits_injective

-- Ray-one membership unfolds to the ray-one property.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    u ∈ integralRayOneUnits m ↔
      IsRayElementOne m
        ((integralUnitsToRayElements m u : rayElements m) : Kˣ) :=
  mem_integralRayOneUnits_iff m u

-- Quotient representative evaluation.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToRayQuotient m u =
      QuotientGroup.mk (integralUnitsToRayElements m u) :=
  integralUnitsToRayQuotient_apply m u

-- Residue-sign evaluation.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToResidueSign m u =
      residueSignMap m (integralUnitsToRayElements m u) :=
  integralUnitsToResidueSign_apply m u

-- Both kernel theorems.
example (m : Modulus K) :
    (integralUnitsToRayQuotient m).ker = integralRayOneUnits m :=
  integralUnitsToRayQuotient_ker m

example (m : Modulus K) :
    (integralUnitsToResidueSign m).ker = integralRayOneUnits m :=
  integralUnitsToResidueSign_ker m

-- Injectivity of the ray-one inclusion.
example (m : Modulus K) :
    Function.Injective (integralRayOneUnitsInclusion m) :=
  integralRayOneUnitsInclusion_injective m

-- Both MulExact results.
example (m : Modulus K) :
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToRayQuotient m) :=
  integralUnits_mulExact_quotient m

example (m : Modulus K) :
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToResidueSign m) :=
  integralUnits_mulExact_residueSign m

end IntegralUnitsTest
