module

public import Mathlib
public import Instance.PDivisibleGroup_Basic
public import Structure.PDivisibleGroup_Basic
public import Abbrev.PDivisibleGroup_Basic

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w


namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

def height (_G : PDivisibleGroup R p h) : ℕ := h

end PDivisibleGroup

end
