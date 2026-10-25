import Structure.GroupCohomology_Selmer
import Def.GroupCohomology_SelmerLe

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ) (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


structure IsGreenbergWilesLeDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLe loc M M' pairing L


end groupCohomology
