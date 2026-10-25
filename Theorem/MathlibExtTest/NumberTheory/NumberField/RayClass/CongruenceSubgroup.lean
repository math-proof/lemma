/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean -/

import Def.NumberTheory.NumberField.RayClass.CongruenceSubgroup
import Lemma.Nat.NumberField.RayClass.CongruenceSubgroup
variable {K : Type*} [Field K] [NumberField K]
variable {m : NumberField.Modulus K}


-- Containment field.
example (C : NumberField.Modulus.CongruenceSubgroup (K := K) m) :
    NumberField.Modulus.rayGroup m ≤ C.toSubgroup :=
  C.rayGroup_le

-- Comap of the image recovers the subgroup.
example (C : NumberField.Modulus.CongruenceSubgroup (K := K) m) :
    C.image.comap (NumberField.Modulus.rayClassMap m) = C.toSubgroup :=
  NumberField.Modulus.CongruenceSubgroup.image_comap C

-- Ambient subgroup lies inside the coprime ideals.
example (C : NumberField.Modulus.CongruenceSubgroup (K := K) m) :
    C.toAmbientSubgroup ≤ NumberField.Modulus.coprimeFractionalIdeals m :=
  NumberField.Modulus.CongruenceSubgroup.toAmbientSubgroup_le C

-- Smallest/largest images are bottom/top.
example (m : NumberField.Modulus K) :
    (NumberField.Modulus.CongruenceSubgroup.smallest (K := K) m).image = ⊥ :=
  NumberField.Modulus.CongruenceSubgroup.smallest_image m

example (m : NumberField.Modulus K) :
    (NumberField.Modulus.CongruenceSubgroup.largest (K := K) m).image = ⊤ :=
  NumberField.Modulus.CongruenceSubgroup.largest_image m

-- Existential image membership from subgroup membership.
example (C : NumberField.Modulus.CongruenceSubgroup (K := K) m)
    (y : NumberField.Modulus.coprimeFractionalIdeals m)
    (hy : y ∈ C.toSubgroup) :
    NumberField.Modulus.rayClassMap m y ∈ C.image := by
  rw [NumberField.Modulus.CongruenceSubgroup.mem_image_iff]
  exact ⟨y, hy, rfl⟩

