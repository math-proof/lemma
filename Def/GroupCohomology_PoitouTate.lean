import Mathlib
import Lemma.GroupCohomology.Selmer

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

noncomputable def locTotal : H1 M →ₗ[k] ∀ v, H1 (Rep.res (loc v) M) :=
  LinearMap.pi fun v => (locRes loc M v).hom

end TotalLocalization

section TotalPairing

variable [Fintype ι] (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def totalPairing :
    (∀ v, H1 (Rep.res (loc v) M)) →ₗ[k] (∀ v, H1 (Rep.res (loc v) M')) →ₗ[k] k :=
  ∑ v, (pairing v).compl₁₂ (LinearMap.proj v) (LinearMap.proj v)

end TotalPairing

end groupCohomology
