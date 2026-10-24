import Mathlib
import Lemma.Definitions.Def_GroupCohomology_Selmer

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

@[simp]
lemma locTotal_apply (x : H1 M) (v : ι) :
    locTotal loc M x v = (locRes loc M v).hom x := rfl

end TotalLocalization

section TotalPairing

variable [Fintype ι] (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def totalPairing :
    (∀ v, H1 (Rep.res (loc v) M)) →ₗ[k] (∀ v, H1 (Rep.res (loc v) M')) →ₗ[k] k :=
  ∑ v, (pairing v).compl₁₂ (LinearMap.proj v) (LinearMap.proj v)

@[simp]
lemma totalPairing_apply (x : ∀ v, H1 (Rep.res (loc v) M))
    (y : ∀ v, H1 (Rep.res (loc v) M')) :
    totalPairing loc M M' pairing x y = ∑ v, pairing v (x v) (y v) := by
  simp only [totalPairing, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]

structure IsPoitouTateOrthogonality : Prop where

  annihilator_fst :
    orthogonal (totalPairing loc M M' pairing) (LinearMap.range (locTotal loc M))
      = LinearMap.range (locTotal loc M')

  annihilator_snd :
    orthogonal (totalPairing loc M M' pairing).flip (LinearMap.range (locTotal loc M'))
      = LinearMap.range (locTotal loc M)

end TotalPairing

end groupCohomology
