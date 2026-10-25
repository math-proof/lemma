-- Carved from Lemma/Definitions/Def_GroupCohomology_SelmerAdm.lean: instance decls only.
import Mathlib
import Lemma.GroupCohomology.SelmerLe
import Lemma.GroupCohomology.SelmerAdm

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

instance finiteDimensional_selmerAdm_of_adm
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (adm : Submodule k (H1 M))
    [FiniteDimensional k adm] : FiniteDimensional k (selmerAdm loc M L adm) :=
  Submodule.finiteDimensional_inf_right _ _

variable [Fintype ι] (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

end groupCohomology
