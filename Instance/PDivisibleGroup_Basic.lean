-- Carved from Lemma/Definitions/Def_PDivisibleGroup_Basic.lean: instance decls only.
import Mathlib

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w


namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

instance instModuleFlat (v : ℕ) : Module.Flat R (G.level v) := inferInstance

end PDivisibleGroup
