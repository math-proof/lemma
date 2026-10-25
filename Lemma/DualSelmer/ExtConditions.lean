import Lemma.GroupCohomology.Selmer
import Def.DualSelmer_ExtConditions
import Abbrev.DualSelmer_ExtConditions

set_option autoImplicit false

open CategoryTheory Module Classical

universe u

namespace groupCohomology

variable {k : Type u} [Field k] {Γ : Type u} [Group Γ]


lemma extConditions_of_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∈ P) : extConditions loc M P U v = ⊥ := by
  simp [extConditions, hv]

lemma extConditions_of_not_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∉ P) : extConditions loc M P U v = U v := by
  simp [extConditions, hv]

end groupCohomology
