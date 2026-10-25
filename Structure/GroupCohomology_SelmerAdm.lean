import Mathlib
import Structure.GroupCohomology_SelmerLe
import Instance.GroupCohomology_SelmerAdm
import Def.GroupCohomology_SelmerAdm

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)


variable [Fintype ι] (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


structure IsGreenbergWilesLeDatumAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop where

  finite_selmer : FiniteDimensional k (selmerAdm loc M L adm)

  finite_dualSelmer :
    FiniteDimensional k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLeAdm loc M M' pairing L adm adm'


end groupCohomology
