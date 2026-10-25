/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/CongruenceSubgroup.lean -/

import Def.NumberTheory.NumberField.RayClass.Group
import Lemma.Nat.NumberField.RayClass.Group
import Structure.NumberTheory.NumberField.RayClass.CongruenceSubgroup
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

namespace CongruenceSubgroup

variable {m : Modulus K}

/-- Image of a congruence subgroup in the ray class group. -/
def image (C : CongruenceSubgroup (K := K) m) :
    Subgroup (RayClassGroup m) :=
  C.toSubgroup.map (rayClassMap m)

/-- Ambient subgroup of all units via the subtype inclusion. -/
def toAmbientSubgroup (C : CongruenceSubgroup (K := K) m) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  C.toSubgroup.map (coprimeFractionalIdeals m).subtype

/-- Smallest congruence subgroup, given by the ray group. -/
def smallest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨rayGroup m, le_rfl⟩

/-- Largest congruence subgroup, given by the full group. -/
def largest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨⊤, le_top⟩

end CongruenceSubgroup
end NumberField.Modulus
end
