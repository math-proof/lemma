import Mathlib
import Instance.PDivisibleGroup_Basic
import Structure.PDivisibleGroup_Basic

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w

namespace PDivisibleGroup.Hopf

section NSMul

variable (R : Type u) [CommSemiring R] (A : Type v) [CommSemiring A] [Bialgebra R A]


end NSMul

section Ideals

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]


end Ideals

end PDivisibleGroup.Hopf


namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

abbrev transitionAlgHom (v : ℕ) : G.level (v + 1) →ₐ[R] G.level v :=
  (G.transition v : G.level (v + 1) →ₐ[R] G.level v)

end PDivisibleGroup
