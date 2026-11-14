import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.RayClass.CongruenceSubgroup
open scoped nonZeroDivisors
open NumberField.Modulus
open CongruenceSubgroup


namespace NumberField.Modulus.CongruenceSubgroup

/--
[mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma mem_image_iff
  [Field K] [NumberField K]
  {m : Modulus K}
  {C : CongruenceSubgroup (K := K) m}
  {x : RayClassGroup m} :
-- imply
  x ∈ C.image ↔ ∃ y ∈ C.toSubgroup, rayClassMap m y = x :=
-- proof
  Subgroup.mem_map

end NumberField.Modulus.CongruenceSubgroup

namespace NumberField.Modulus.CongruenceSubgroup

/--
[image_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma image_comap
  [Field K] [NumberField K]
  {m : Modulus K}
  (C : CongruenceSubgroup (K := K) m) :
-- imply
  C.image.comap (rayClassMap m) = C.toSubgroup := by
-- proof
  unfold image
  rw [Subgroup.comap_map_eq, rayClassMap_ker, sup_eq_left]
  exact C.rayGroup_le

end NumberField.Modulus.CongruenceSubgroup

namespace NumberField.Modulus.CongruenceSubgroup

/--
[toAmbientSubgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean)
-/
@[path]
lemma toAmbientSubgroup_le
  [Field K] [NumberField K]
  {m : Modulus K}
  (C : CongruenceSubgroup (K := K) m) :
-- imply
  C.toAmbientSubgroup ≤ coprimeFractionalIdeals m := by
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
  (smallest (K := K) m).image = ⊥ := by
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
  (largest (K := K) m).image = ⊤ := by
-- proof
  rw [image, largest, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := rayClassMap_surjective x
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)

end NumberField.Modulus.CongruenceSubgroup


-- created on 2026-10-20
-- updated on 2026-11-13
