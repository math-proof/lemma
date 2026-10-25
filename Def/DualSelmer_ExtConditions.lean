import Lemma.GroupCohomology.Selmer

set_option autoImplicit false

open CategoryTheory Module Classical

universe u

namespace groupCohomology

variable {k : Type u} [Field k] {Γ : Type u} [Group Γ]


variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def extConditions (P : Set ι)
    (U : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M)) :=
  if v ∈ P then ⊥ else U v

end groupCohomology
