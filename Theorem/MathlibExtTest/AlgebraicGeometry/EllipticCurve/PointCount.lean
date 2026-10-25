/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF


namespace WeierstrassCurve.Affine.PointCountTest

open WeierstrassCurve

universe u

example {R : Type u} [CommRing R] [Finite R] (W : Affine R) : Finite W.Point :=
  inferInstance

variable {F : Type u} [Field F] [Finite F] (W : Affine F) [W.IsElliptic]

example : W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
  W.frobeniusTrace_eq

example : Nat.card W.Point = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 :=
  W.natCard_point_eq_natCard_affineSolutions_add_one

example : Nat.card W.Point ≤ 2 * Nat.card F + 1 :=
  W.natCard_point_le_two_mul_natCard_add_one

example : (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace :=
  W.natCard_point_eq_natCard_add_one_sub_frobeniusTrace

example : (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 :=
  W.natCard_point_add_frobeniusTrace_eq

end WeierstrassCurve.Affine.PointCountTest
