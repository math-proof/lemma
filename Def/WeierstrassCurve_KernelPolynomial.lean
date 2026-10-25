import Mathlib

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def kernelPolynomial (S : Finset (R × R)) : R[X] :=
  ∏ P ∈ S, (X - C P.1)

end WeierstrassCurve
