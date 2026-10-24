import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.CongruenceSubgroup
open scoped nonZeroDivisors
open NumberField.Modulus
open CongruenceSubgroup


namespace NumberField.Modulus.CongruenceSubgroup

/--
[mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma mem_image_iff
  :
-- imply
  {K : Type*}
    [Field K]
    [NumberField K]
    {m : Modulus K}
    (C : CongruenceSubgroup (K :=
-- proof
  Subgroup.mem_map
@[simp] theorem image_comap (C : CongruenceSubgroup (K := K) m) :
  C.image.comap (rayClassMap m) = C.toSubgroup := by
  unfold image
  rwa [Subgroup.comap_map_eq, sup_eq_left, rayClassMap_ker]

end NumberField.Modulus.CongruenceSubgroup

namespace NumberField.Modulus.CongruenceSubgroup

/--
[toAmbientSubgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma toAmbientSubgroup_le
  :
-- imply
  {K : Type*}
    [Field K]
    [NumberField K]
    {m : Modulus K}
    (C : CongruenceSubgroup (K := by
-- proof
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.property

end NumberField.Modulus.CongruenceSubgroup

namespace NumberField.Modulus.CongruenceSubgroup

/--
[smallest_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma smallest_image
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (smallest (K := by
-- proof
  rw [image, smallest, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rwa [Subgroup.mem_bot, rayClassMap_eq_one_iff]

end NumberField.Modulus.CongruenceSubgroup

namespace NumberField.Modulus.CongruenceSubgroup

/--
[largest_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma largest_image
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (largest (K := by
-- proof
  rw [image, largest, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := rayClassMap_surjective m x
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)

end NumberField.Modulus.CongruenceSubgroup

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


-- created on 2026-10-20
-- updated on 2026-10-23
