import Mathlib
import Lemma.Dieudonne.DatumAndHonda

set_option autoImplicit false

open scoped TensorProduct
open Deformation

universe u v w

section Realization

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A]

noncomputable def primitives : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

end Realization
