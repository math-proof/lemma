import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.RayClass.Group
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[rayClassMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
lemma rayClassMap_surjective
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (rayClassMap (K :=
-- proof
  QuotientGroup.mk'_surjective _
@[simp] theorem rayClassMap_ker (m : Modulus K) :
  MonoidHom.ker (rayClassMap (K := K) m) = rayGroup m :=
  QuotientGroup.ker_mk' _
@[simp] theorem rayClassMap_eq_one_iff (m : Modulus K)
  (x : coprimeFractionalIdeals m) :
  rayClassMap m x = 1 ↔ x ∈ rayGroup m :=
  QuotientGroup.eq_one_iff x

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClassMap_eq_rayClassMap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Group.lean)
-/
@[path]
lemma rayClassMap_eq_rayClassMap_iff
  [Field K] [NumberField K]
  {m : Modulus K}
  {a b : coprimeFractionalIdeals m} :
-- imply
  rayClassMap m a = rayClassMap m b ↔ a / b ∈ rayGroup m := by
-- proof
simpa [rayClassMap, RayClassGroup] using
  (QuotientGroup.eq_iff_div_mem (N := rayGroup m) (x := a) (y := b))

end NumberField.Modulus

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


-- created on 2026-10-20
-- updated on 2026-10-26
