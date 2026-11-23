module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.NumberTheory.NumberField.RayClass.IntegralUnits.Part4

public noncomputable section

open NumberField
open Modulus

set_option synthInstance.maxHeartbeats 100000
noncomputable section


set_option linter.defProp false

namespace NumberField.Modulus

/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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
public theorem integralUnits_mulExact_residueSign
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


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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
public theorem integralUnits_mulExact_residueSign
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
public theorem integralUnitsToRayElements_coe_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    integralUnitsToFieldUnits u := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_coe

/--
[mem_integralRayOneUnits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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
public theorem integralUnits_mulExact_residueSign
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
public theorem integralUnitsToRayElements_coe_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    integralUnitsToFieldUnits u := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_coe

/--
[mem_integralRayOneUnits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem mem_integralRayOneUnits_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  u ∈ integralRayOneUnits m ↔
    IsRayElementOne m
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_integralRayOneUnits_iff

/--
[integralUnitsToRayQuotient_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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
public theorem integralUnits_mulExact_residueSign
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
public theorem integralUnitsToRayElements_coe_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    integralUnitsToFieldUnits u := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_coe

/--
[mem_integralRayOneUnits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem mem_integralRayOneUnits_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  u ∈ integralRayOneUnits m ↔
    IsRayElementOne m
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_integralRayOneUnits_iff

/--
[integralUnitsToRayQuotient_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayQuotient_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  integralUnitsToRayQuotient m u =
    QuotientGroup.mk (integralUnitsToRayElements m u) := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayQuotient_apply

/--
[integralUnitsToResidueSign_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/


/--
[integralUnitsToFieldUnits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToFieldUnits_injective
  [Field K] [NumberField K] :
-- imply
  Function.Injective (integralUnitsToFieldUnits (K := K)) :=
-- proof
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayElements_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayElements_injective
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
public theorem integralRayOneUnitsInclusion_injective
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
public theorem integralUnits_mulExact_quotient
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
public theorem integralUnits_mulExact_residueSign
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
public theorem integralUnitsToRayElements_coe_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    integralUnitsToFieldUnits u := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayElements_coe

/--
[mem_integralRayOneUnits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem mem_integralRayOneUnits_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  u ∈ integralRayOneUnits m ↔
    IsRayElementOne m
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_integralRayOneUnits_iff

/--
[integralUnitsToRayQuotient_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToRayQuotient_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  integralUnitsToRayQuotient m u =
    QuotientGroup.mk (integralUnitsToRayElements m u) := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayQuotient_apply

/--
[integralUnitsToResidueSign_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
@[path]
public theorem integralUnitsToResidueSign_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  integralUnitsToResidueSign m u =
    residueSignMap m (integralUnitsToRayElements m u) := by
-- proof
  apply NumberField.Modulus.integralUnitsToResidueSign_apply

/--
[integralUnitsToRayQuotient_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean)
-/
