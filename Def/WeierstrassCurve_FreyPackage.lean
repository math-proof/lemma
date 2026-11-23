/-
Copyright (c) 2024 Kevin Buzzard, Ruben Van de Velde, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Ported from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT, blueprint §2.5–2.6).
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Structure.FLTPrelim_FreyPackage

@[expose] public section

set_option autoImplicit false

namespace FreyPackage

def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

end FreyPackage
