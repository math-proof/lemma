import Mathlib

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

namespace HopfAlgebra

structure FVectStructure (F : Type w) [Field F] (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [Bialgebra R H] where

  act : F → (H →ₐc[R] H)

  act_one : act 1 = BialgHom.id R H

  act_mul : ∀ a b : F, act (a * b) = (act a).comp (act b)

  act_zero : WithConv.toConv (act 0 : H →ₐ[R] H) = (1 : WithConv (H →ₐ[R] H))

  act_add : ∀ a b : F, WithConv.toConv (act (a + b) : H →ₐ[R] H) =
    WithConv.toConv (act a : H →ₐ[R] H) * WithConv.toConv (act b : H →ₐ[R] H)

namespace FVectStructure

variable {F : Type w} [Field F] {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
variable (σ : FVectStructure F R H)


end FVectStructure


namespace IsFCompatible

variable {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    {H'' : Type*} [CommRing H''] [Bialgebra R H'']


end IsFCompatible

namespace FVectStructure

variable (F : Type w) [Field F] (R : Type u) [CommRing R]


end FVectStructure

end HopfAlgebra
