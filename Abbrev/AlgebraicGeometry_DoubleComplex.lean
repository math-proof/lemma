import Mathlib

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex


section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

end E2


end DoubleComplex

end
