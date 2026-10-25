import Mathlib

open MvPolynomial

namespace ProjWeierstrassCubicPrime

section CommRing

variable {F : Type*} [CommRing F]

noncomputable def wCubic (V : WeierstrassCurve.Projective F) : Cubic (MvPolynomial (Fin 2) F) :=
  ⟨1, C V.a₂ * X 1, C V.a₄ * X 1 ^ 2 - C V.a₁ * X 0 * X 1,
    C V.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1 - C V.a₃ * X 0 * X 1 ^ 2⟩

end CommRing


section Gates

def gateCurveA : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def gateCurveB : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 0⟩

end Gates

end ProjWeierstrassCubicPrime
