import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.Group
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[rayClassMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
private lemma rayClassMap_surjective_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (rayClassMap (K := by
-- proof
  apply NumberField.Modulus.rayClassMap_surjective m

/--
[rayClassMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
private lemma rayClassMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  MonoidHom.ker (rayClassMap (K := by
-- proof
  apply NumberField.Modulus.rayClassMap_ker m

/--
[rayClassMap_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
private lemma rayClassMap_eq_one_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : coprimeFractionalIdeals m} :
-- imply
  rayClassMap m x = 1 ↔ x ∈ rayGroup m := by
-- proof
  apply NumberField.Modulus.rayClassMap_eq_one_iff m x

/--
[rayClassMap_eq_rayClassMap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
private lemma rayClassMap_eq_rayClassMap_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {a b : coprimeFractionalIdeals m} :
-- imply
  rayClassMap m a = rayClassMap m b ↔ a / b ∈ rayGroup m := by
-- proof
  apply NumberField.Modulus.rayClassMap_eq_rayClassMap_iff m a b


-- created on 2026-10-20
