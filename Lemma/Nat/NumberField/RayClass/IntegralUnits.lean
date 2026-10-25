import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.RayClass.IntegralUnits.Part4
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
lemma integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
lemma integralUnitsToRayElements_injective
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralUnitsToRayElements m) :=
-- proof
  (MonoidHom.injective_codRestrict _ _ _).mpr
    integralUnitsToFieldUnits_injective

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralRayOneUnitsInclusion_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
lemma integralRayOneUnitsInclusion_injective
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) := by
-- proof
  intro a b h
  have h' : (a : (𝓞 K)ˣ) = (b : (𝓞 K)ˣ) := h
  exact Subtype.ext h'

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnits_mulExact_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
lemma integralUnits_mulExact_quotient
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToRayQuotient m) := by
-- proof
  rw [MonoidHom.mulExact_iff, integralUnitsToRayQuotient_ker]
  exact (Subgroup.range_subtype _).symm

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnits_mulExact_residueSign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
lemma integralUnits_mulExact_residueSign
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToResidueSign m) := by
-- proof
  rw [MonoidHom.mulExact_iff, integralUnitsToResidueSign_ker]
  exact (Subgroup.range_subtype _).symm

end NumberField.Modulus

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


-- created on 2026-10-20
-- updated on 2026-10-23
