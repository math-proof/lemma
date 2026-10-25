import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]


end Rep

namespace groupCohomology

section CupProduct

variable {k G : Type u} [CommRing k] [Group G] {A B N : Rep k G}


variable (φ : A →ₗ[k] B →ₗ[k] N)


variable (hφ : Rep.IsEquivariantBilinear A B N φ)

include hφ in


section DescentGadget

variable {W : Type u} [AddCommGroup W] [Module k W]

variable (A) in


end DescentGadget


def IsCupProductPairing (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop :=
  ∀ (f : cocycles₁ A) (g : cocycles₁ B),
    P (H1π A f) (H1π B g) = inv (H2π N (cup φ hφ f g))

structure IsLocalTateDatum (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop where

  left_nondegenerate : ∀ a : A, (∀ b : B, φ a b = 0) → a = 0

  right_nondegenerate : ∀ b : B, (∀ a : A, φ a b = 0) → b = 0

  finrank_H2 : Module.finrank k (H2 N) = 1

  inv_ne_zero : inv ≠ 0

  cup_eq : IsCupProductPairing φ hφ inv P

end CupProduct

section Arithmetic

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


end Arithmetic

section LocalDuality

variable {k G : Type u} [Field k] [Group G] {A B N : Rep k G}
variable (φ : A →ₗ[k] B →ₗ[k] N)
variable (hφ : Rep.IsEquivariantBilinear A B N φ)

structure IsLocalTateDuality (inv : H2 N →ₗ[k] k) (P : H1 A →ₗ[k] H1 B →ₗ[k] k) : Prop where

  toIsLocalTateDatum : IsLocalTateDatum φ hφ inv P

  finite_H1_left : FiniteDimensional k (H1 A)

  finite_H1_right : FiniteDimensional k (H1 B)

  nondegenerate : P.Nondegenerate

end LocalDuality

section Family

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)


end Family

end groupCohomology
