/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.Group
/-!
# Congruence subgroups (N419 Definition 22.1)
A congruence subgroup is a subgroup of the coprime ideals
containing the ray group. Its image in the ray class group,
ambient version, smallest/largest examples follow.
-/

noncomputable section
open scoped nonZeroDivisors

namespace NumberField.Modulus
variable {K : Type*} [Field K] [NumberField K]

/-- Congruence subgroup for `m`: subgroup of coprime ideals
containing the ray group. -/
@[ext] structure CongruenceSubgroup (m : Modulus K) where
  /-- Underlying subgroup of the coprime ideals. -/
  toSubgroup : Subgroup (coprimeFractionalIdeals m)
  /-- The ray group is contained in the subgroup. -/
  rayGroup_le : rayGroup m ≤ toSubgroup

namespace CongruenceSubgroup
variable {m : Modulus K}

/-- Image of a congruence subgroup in the ray class group. -/
def image (C : CongruenceSubgroup (K := K) m) :
    Subgroup (RayClassGroup m) :=
  C.toSubgroup.map (rayClassMap m)

/-- Membership in the image is existential over the subgroup. -/
theorem mem_image_iff (C : CongruenceSubgroup (K := K) m)
    (x : RayClassGroup m) :
    x ∈ C.image ↔ ∃ y ∈ C.toSubgroup, rayClassMap m y = x :=
  Subgroup.mem_map

@[simp] theorem image_comap (C : CongruenceSubgroup (K := K) m) :
    C.image.comap (rayClassMap m) = C.toSubgroup := by
  unfold image
  rw [Subgroup.comap_map_eq, sup_eq_left, rayClassMap_ker]
  exact C.rayGroup_le

/-- Ambient subgroup of all units via the subtype inclusion. -/
def toAmbientSubgroup (C : CongruenceSubgroup (K := K) m) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  C.toSubgroup.map (coprimeFractionalIdeals m).subtype

theorem toAmbientSubgroup_le (C : CongruenceSubgroup (K := K) m) :
    C.toAmbientSubgroup ≤ coprimeFractionalIdeals m := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.property

/-- Smallest congruence subgroup, given by the ray group. -/
def smallest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨rayGroup m, le_rfl⟩

/-- Largest congruence subgroup, given by the full group. -/
def largest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨⊤, le_top⟩

theorem smallest_image (m : Modulus K) :
    (smallest (K := K) m).image = ⊥ := by
  rw [image, smallest, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_bot, rayClassMap_eq_one_iff]
  exact hy

theorem largest_image (m : Modulus K) :
    (largest (K := K) m).image = ⊤ := by
  rw [image, largest, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := rayClassMap_surjective m x
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)

end CongruenceSubgroup
end NumberField.Modulus
