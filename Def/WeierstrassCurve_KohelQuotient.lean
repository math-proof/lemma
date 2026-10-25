import Mathlib
import Def.WeierstrassCurve_VeluQuotientOfSums

set_option autoImplicit false

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

def rootESymm (h : R[X]) (k : ℕ) : R :=
  if k ≤ h.natDegree then (-1) ^ k * h.coeff (h.natDegree - k) else 0

def rootPowerSumOne (h : R[X]) : R := h.rootESymm 1

def rootPowerSumTwo (h : R[X]) : R := h.rootESymm 1 ^ 2 - 2 * h.rootESymm 2

def rootPowerSumThree (h : R[X]) : R :=
  h.rootESymm 1 ^ 3 - 3 * h.rootESymm 1 * h.rootESymm 2 + 3 * h.rootESymm 3

end Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def kohelT (h : R[X]) : R :=
  6 * h.rootPowerSumTwo + W.b₂ * h.rootPowerSumOne + h.natDegree * W.b₄

def kohelW (h : R[X]) : R :=
  10 * h.rootPowerSumThree + 2 * W.b₂ * h.rootPowerSumTwo + 3 * W.b₄ * h.rootPowerSumOne
    + h.natDegree * W.b₆

def kohelQuotient (h : R[X]) : WeierstrassCurve R :=
  W.veluQuotientOfSums (W.kohelT h) (W.kohelW h)

end WeierstrassCurve
