import Mathlib
import Structure.GroupCohomology_Selmer
import Def.GroupCohomology_PoitouTate

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ)

section TotalLocalization

variable (M : Rep k Γ)


end TotalLocalization

section TotalPairing

variable [Fintype ι] (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


structure IsPoitouTateOrthogonality : Prop where

  annihilator_fst :
    orthogonal (totalPairing loc M M' pairing) (LinearMap.range (locTotal loc M))
      = LinearMap.range (locTotal loc M')

  annihilator_snd :
    orthogonal (totalPairing loc M M' pairing).flip (LinearMap.range (locTotal loc M'))
      = LinearMap.range (locTotal loc M)

end TotalPairing

end groupCohomology
