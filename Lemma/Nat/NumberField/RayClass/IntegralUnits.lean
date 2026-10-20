import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.IntegralUnits
open NumberField
open Modulus


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToFieldUnits_injective_eq
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := by
-- proof
  apply NumberField.Modulus.integralUnitsToFieldUnits_injective

/--
[integralUnitsToRayElements_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToRayElements_coe_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    integralUnitsToFieldUnits u := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_coe m u

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToRayElements_injective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralUnitsToRayElements m) := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_injective m

/--
[mem_integralRayOneUnits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma mem_integralRayOneUnits_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  u ∈ integralRayOneUnits m ↔
    IsRayElementOne m
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_integralRayOneUnits_iff m u

/--
[integralUnitsToRayQuotient_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToRayQuotient_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  integralUnitsToRayQuotient m u =
    QuotientGroup.mk (integralUnitsToRayElements m u) := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayQuotient_apply m u

/--
[integralUnitsToResidueSign_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToResidueSign_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  integralUnitsToResidueSign m u =
    residueSignMap m (integralUnitsToRayElements m u) := by
-- proof
  apply NumberField.Modulus.integralUnitsToResidueSign_apply m u

/--
[integralUnitsToRayQuotient_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToRayQuotient_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (integralUnitsToRayQuotient m).ker = integralRayOneUnits m := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayQuotient_ker m

/--
[integralUnitsToResidueSign_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnitsToResidueSign_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (integralUnitsToResidueSign m).ker = integralRayOneUnits m := by
-- proof
  apply NumberField.Modulus.integralUnitsToResidueSign_ker m

/--
[integralRayOneUnitsInclusion_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralRayOneUnitsInclusion_injective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) := by
-- proof
  apply NumberField.Modulus.integralRayOneUnitsInclusion_injective m

/--
[integralUnits_mulExact_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnits_mulExact_quotient_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToRayQuotient m) := by
-- proof
  apply NumberField.Modulus.integralUnits_mulExact_quotient m

/--
[integralUnits_mulExact_residueSign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
private lemma integralUnits_mulExact_residueSign_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToResidueSign m) := by
-- proof
  apply NumberField.Modulus.integralUnits_mulExact_residueSign m


-- created on 2026-10-20
