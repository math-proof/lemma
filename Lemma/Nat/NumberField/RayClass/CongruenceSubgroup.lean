import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.CongruenceSubgroup
open scoped nonZeroDivisors
open NumberField.Modulus
open CongruenceSubgroup


/--
[mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
private lemma mem_image_iff_eq
  :
-- imply
  {K : Type*}
    [Field K]
    [NumberField K]
    {m : Modulus K}
    (C : CongruenceSubgroup (K := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.mem_image_iff

/--
[image_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
private lemma image_comap_eq
  :
-- imply
  {K : Type*}
    [Field K]
    [NumberField K]
    {m : Modulus K}
    (C : CongruenceSubgroup (K := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.image_comap

/--
[toAmbientSubgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
private lemma toAmbientSubgroup_le_eq
  :
-- imply
  {K : Type*}
    [Field K]
    [NumberField K]
    {m : Modulus K}
    (C : CongruenceSubgroup (K := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.toAmbientSubgroup_le

/--
[smallest_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
private lemma smallest_image_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (smallest (K := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.smallest_image m

/--
[largest_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
private lemma largest_image_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (largest (K := by
-- proof
  apply NumberField.Modulus.CongruenceSubgroup.largest_image m


-- created on 2026-10-20
