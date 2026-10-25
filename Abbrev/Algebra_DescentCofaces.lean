import Mathlib

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

noncomputable section

namespace Algebra.DescentCofaces

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

abbrev R₂ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)

abbrev R₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))

end Algebra.DescentCofaces

end
