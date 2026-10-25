import Mathlib
import Def.WeierstrassCurve_VeluQuotientMap
import Macro.WeierstrassCurve_VeluPointMap

open Polynomial
open scoped WeierstrassCurve.VeluPointMap

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


def veluXNum (x₀ y₀ x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀

def veluYNum (x₀ y₀ x y : R) : R :=
  y * (x - x₀) ^ 3 - (W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
    + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀))

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def veluY (S : Finset (F × F)) (x y : F) : F :=
  y - ∑ Q ∈ S, (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
    + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
    + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2)

end Field

end WeierstrassCurve
