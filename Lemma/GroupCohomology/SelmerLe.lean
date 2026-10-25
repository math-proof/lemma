import Lemma.GroupCohomology.Selmer
import Def.GroupCohomology_SelmerLe
import Structure.GroupCohomology_SelmerLe

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ) (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


theorem greenbergWilesLe_of_greenbergWilesEq
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : greenbergWilesEq loc M M' pairing L) : greenbergWilesLe loc M M' pairing L :=
  le_of_eq h


theorem IsGreenbergWilesDatum.toLe {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    IsGreenbergWilesLeDatum loc M M' pairing L where
  finite_selmer := h.finite_selmer
  finite_dualSelmer := h.finite_dualSelmer
  finite_local := h.finite_local
  le := greenbergWilesLe_of_greenbergWilesEq loc M M' pairing h.formula


theorem selmerComparisonStep_refl (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerComparisonStep loc M M' pairing L L := fun _ => le_refl _

end groupCohomology
