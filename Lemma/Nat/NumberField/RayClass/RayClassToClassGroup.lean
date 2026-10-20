import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.RayClassToClassGroup
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[coprimeIdealClassMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma coprimeIdealClassMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : coprimeFractionalIdeals m} :
-- imply
  coprimeIdealClassMap m I =
    ClassGroup.mk K ((coprimeFractionalIdeals m).subtype I) := by
-- proof
  apply NumberField.Modulus.coprimeIdealClassMap_apply m I

/--
[rayGroup_le_coprimeIdealClassMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayGroup_le_coprimeIdealClassMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroup m ≤ (coprimeIdealClassMap m).ker := by
-- proof
  apply NumberField.Modulus.rayGroup_le_coprimeIdealClassMap_ker m

/--
[rayClassToClassGroup_rayClassMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_rayClassMap_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : coprimeFractionalIdeals m} :
-- imply
  rayClassToClassGroup m (rayClassMap m I) = coprimeIdealClassMap m I := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_rayClassMap m I

/--
[rayClassToClassGroup_comp_rayClassMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_comp_rayClassMap_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayClassToClassGroup m).comp (rayClassMap m) = coprimeIdealClassMap m := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_comp_rayClassMap m

/--
[rayClassToClassGroup_rayQuotientToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_rayQuotientToRayClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayClassToClassGroup m (rayQuotientToRayClassGroup m (QuotientGroup.mk x)) =
    coprimeIdealClassMap m (principalRayIdealMap m x) := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_rayQuotientToRayClassGroup m x

/--
[rayClassToClassGroup_residueSignToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_residueSignToRayClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayClassToClassGroup m
    (residueSignToRayClassGroup m (residueSignMap m x)) =
    coprimeIdealClassMap m (principalRayIdealMap m x) := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_residueSignToRayClassGroup m x

/--
[rayClassToClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayClassToClassGroup_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayClassToClassGroup m).ker =
    MonoidHom.range (rayQuotientToRayClassGroup m) := by
-- proof
  apply NumberField.Modulus.rayClassToClassGroup_ker m

/--
[rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (rayQuotientToRayClassGroup m)
    (rayClassToClassGroup m) := by
-- proof
  apply NumberField.Modulus.rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup m

/--
[residueSignToRayClassGroup_mulExact_rayClassToClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_mulExact_rayClassToClassGroup_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (residueSignToRayClassGroup m)
    (rayClassToClassGroup m) := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_mulExact_rayClassToClassGroup m


-- created on 2026-10-20
