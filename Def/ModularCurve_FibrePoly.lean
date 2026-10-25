import Mathlib
import Def.ModularCurve_KroneckerTransport

noncomputable section

open Polynomial

namespace ModularCurve

section FibrePoly

variable {k : Type*} [Field k]

def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

end FibrePoly

end ModularCurve

end
