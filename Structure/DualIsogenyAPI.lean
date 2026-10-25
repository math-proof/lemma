import Mathlib

set_option autoImplicit false

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

structure IsDualPair (φ : A →+ B) (ψ : B →+ A) (n : ℤ) : Prop where

  comp_left : ∀ a, ψ (φ a) = n • a

  comp_right : ∀ b, φ (ψ b) = n • b


end AddMonoidHom

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A]

structure DualEndData (φ : AddMonoid.End A) where

  dual : AddMonoid.End A

  trace : ℤ

  norm : ℤ

  add_dual : φ + dual = (trace : AddMonoid.End A)

  mul_dual : φ * dual = (norm : AddMonoid.End A)

  dual_mul : dual * φ = (norm : AddMonoid.End A)

namespace DualEndData

variable {φ : AddMonoid.End A}


end DualEndData


end AddMonoid.End

section NamedResiduals

variable {A : Type*} [AddCommGroup A]


end NamedResiduals

section SatGates


end SatGates
