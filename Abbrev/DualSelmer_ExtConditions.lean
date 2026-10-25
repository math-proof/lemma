import Structure.GroupCohomology_Selmer

set_option autoImplicit false

open CategoryTheory Module Classical

universe u

namespace groupCohomology

variable {k : Type u} [Field k] {Γ : Type u} [Group Γ]

noncomputable abbrev ofChar (ψ : Γ →* kˣ) : Rep k Γ :=
  Rep.of ((Representation.trivial k Γ k).twist ψ)

variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)


end groupCohomology
