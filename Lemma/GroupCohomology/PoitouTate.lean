import Mathlib
import Lemma.GroupCohomology.Selmer
import Def.GroupCohomology_PoitouTate
import Structure.GroupCohomology_PoitouTate

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


@[simp]
lemma locTotal_apply (x : H1 M) (v : ι) :
    locTotal loc M x v = (locRes loc M v).hom x := rfl

end TotalLocalization

section TotalPairing

variable [Fintype ι] (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


@[simp]
lemma totalPairing_apply (x : ∀ v, H1 (Rep.res (loc v) M))
    (y : ∀ v, H1 (Rep.res (loc v) M')) :
    totalPairing loc M M' pairing x y = ∑ v, pairing v (x v) (y v) := by
  simp only [totalPairing, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]


end TotalPairing

end groupCohomology
