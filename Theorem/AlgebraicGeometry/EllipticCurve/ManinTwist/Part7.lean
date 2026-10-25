/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part6
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma pZero_equation [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation (pZeroX W) (pZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist, pZeroX, pZeroY]
  have hcubic := aeval_cubic_X_pow_card W
  simp only [cubic, map_add, map_mul, map_pow, aeval_X, aeval_C] at hcubic
  rw [← pow_mul]
  rw [show (Nat.card F + 3) / 2 * 2 = Nat.card F + 3 by
    rw [mul_comm, twice_half_card_add_three hchar]]
  simp only [zero_mul, add_zero]
  calc
    cubicRat W ^ (Nat.card F + 3) =
        cubicRat W ^ 3 * cubicRat W ^ Nat.card F := by
      rw [pow_add]
      ring
    _ = cubicRat W ^ 3 *
        ((RatFunc.X ^ Nat.card F) ^ 3 +
          algebraMap F (RatFunc F) W.a₂ * (RatFunc.X ^ Nat.card F) ^ 2 +
          algebraMap F (RatFunc F) W.a₄ * RatFunc.X ^ Nat.card F +
          algebraMap F (RatFunc F) W.a₆) := by
      rw [← hcubic]
    _ = _ := by
      simp only [RatFunc.algebraMap_eq_C]
      ring

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
