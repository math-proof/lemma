import Mathlib
import Def.GroupCohomology_SelmerLe
import Instance.GroupCohomology_SelmerAdm

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def selmerAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : Submodule k (H1 M) :=
  selmer loc M L ⊓ adm


variable [Fintype ι] (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def greenbergWilesLeAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop :=
  finrank k (selmerAdm loc M L adm)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    ≤ finrank k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

end groupCohomology
