import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)

def veluT (x y : R) : R := 2 * W.veluGx x y - W.a₁ * W.veluGy x y

def veluU (x y : R) : R := W.veluGy x y ^ 2

def veluW (x y : R) : R := W.veluU x y + x * W.veluT x y


variable (S : Finset (R × R))

def veluTSum : R := ∑ P ∈ S, W.veluT P.1 P.2

def veluWSum : R := ∑ P ∈ S, W.veluW P.1 P.2


def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluTSum S
  a₆ := W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S

end WeierstrassCurve
