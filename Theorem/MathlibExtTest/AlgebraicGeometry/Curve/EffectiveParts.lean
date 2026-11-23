/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/Curve/EffectiveParts.lean -/
module

public import Def.AlgebraicGeometry.Curve.EffectiveParts
public import Theorem.Finsupp.DivZeros.eq.Max0
public import Theorem.Finsupp.DivPoles.eq.Max
public import Theorem.Finsupp.DivZeros.ge.Zero
public import Theorem.Finsupp.DivPoles.ge.Zero
public import Theorem.Finsupp.EqSubDivZerosDivPoles
open Finsupp

public section

namespace CurveDivisor

variable {C : Type*} [DecidableEq C]

example (D : CurveDivisor C) (P : C) : divZeros D P = max (D P) 0 := by
  simp

example (D : CurveDivisor C) (P : C) : divPoles D P = max (-(D P)) 0 := by
  simp

example (D : CurveDivisor C) : 0 ≤ divZeros D :=
  DivZeros.ge.Zero

example (D : CurveDivisor C) : 0 ≤ divPoles D :=
  DivPoles.ge.Zero

example (D : CurveDivisor C) : divZeros D - divPoles D = D := by
  simp

example (P : C) : divZeros (Finsupp.single P (5 : ℤ) : CurveDivisor C) P = 5 := by
  simp

example (P : C) : divPoles (Finsupp.single P (5 : ℤ) : CurveDivisor C) P = 0 := by
  simp

example (P : C) : divZeros (Finsupp.single P (-7 : ℤ) : CurveDivisor C) P = 0 := by
  simp

example (P : C) : divPoles (Finsupp.single P (-7 : ℤ) : CurveDivisor C) P = 7 := by
  simp

end CurveDivisor
