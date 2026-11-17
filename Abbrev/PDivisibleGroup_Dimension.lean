module

public import Mathlib
public import Instance.PDivisibleGroup_Basic

set_option autoImplicit false

@[expose] public noncomputable section

open Coalgebra Bialgebra

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

abbrev augIdeal (v : ℕ) : Ideal (G.level v) := Hopf.augIdeal R (G.level v)

abbrev Cotangent (v : ℕ) : Type := (G.augIdeal v).Cotangent

end PDivisibleGroup

end
