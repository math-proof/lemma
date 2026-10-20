import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.QuotientToRayClass
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[rayElementClassMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayElementClassMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayElementClassMap m x = rayClassMap m (principalRayIdealMap m x) := by
-- proof
  apply NumberField.Modulus.rayElementClassMap_apply m x

/--
[rayOneElements_le_rayElementClassMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayOneElements_le_rayElementClassMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayOneElements m ≤ (rayElementClassMap m).ker := by
-- proof
  apply NumberField.Modulus.rayOneElements_le_rayElementClassMap_ker m

/--
[rayQuotientToRayClassGroup_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayQuotientToRayClassGroup_mk_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayQuotientToRayClassGroup m (QuotientGroup.mk x) =
    rayElementClassMap m x := by
-- proof
  apply NumberField.Modulus.rayQuotientToRayClassGroup_mk m x

/--
[principalRayIdealMap_integralUnitsToRayElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma principalRayIdealMap_integralUnitsToRayElements_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  principalRayIdealMap m (integralUnitsToRayElements m u) = 1 := by
-- proof
  apply NumberField.Modulus.principalRayIdealMap_integralUnitsToRayElements m u

/--
[rayQuotientToRayClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayQuotientToRayClassGroup_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayQuotientToRayClassGroup m).ker =
    MonoidHom.range (integralUnitsToRayQuotient m) := by
-- proof
  apply NumberField.Modulus.rayQuotientToRayClassGroup_ker m

/--
[integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralUnitsToRayQuotient m)
    (rayQuotientToRayClassGroup m) := by
-- proof
  apply NumberField.Modulus.integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup m

/--
[residueSignToRayClassGroup_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_equiv_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {q : rayElements m ⧸ rayOneElements m} :
-- imply
  residueSignToRayClassGroup m (rayElementsQuotientEquivResidueSign m q) =
    rayQuotientToRayClassGroup m q := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_equiv m q

/--
[residueSignToRayClassGroup_residueSignMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_residueSignMap_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  residueSignToRayClassGroup m (residueSignMap m x) =
    rayElementClassMap m x := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_residueSignMap m x

/--
[residueSignToRayClassGroup_comp_residueSignMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_comp_residueSignMap_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (residueSignToRayClassGroup m).comp (residueSignMap m) =
    rayElementClassMap m := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_comp_residueSignMap m

/--
[residueSignToRayClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (residueSignToRayClassGroup m).ker =
    MonoidHom.range (integralUnitsToResidueSign m) := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_ker m

/--
[integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralUnitsToResidueSign m)
    (residueSignToRayClassGroup m) := by
-- proof
  apply NumberField.Modulus.integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup m


-- created on 2026-10-20
