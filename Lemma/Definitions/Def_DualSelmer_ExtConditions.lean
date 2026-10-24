import Lemma.Definitions.Def_GroupCohomology_Selmer

set_option autoImplicit false

open CategoryTheory Module Classical

universe u

namespace groupCohomology

variable {k : Type u} [Field k] {Γ : Type u} [Group Γ]

noncomputable abbrev ofChar (ψ : Γ →* kˣ) : Rep k Γ :=
  Rep.of ((Representation.trivial k Γ k).twist ψ)

variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def extConditions (P : Set ι)
    (U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M)) :=
  if v ∈ P then ⊥ else U v

lemma extConditions_of_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∈ P) : extConditions loc M P U v = ⊥ := by
  simp [extConditions, hv]

lemma extConditions_of_not_mem {P : Set ι} {U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    {v : ι} (hv : v ∉ P) : extConditions loc M P U v = U v := by
  simp [extConditions, hv]

end groupCohomology
