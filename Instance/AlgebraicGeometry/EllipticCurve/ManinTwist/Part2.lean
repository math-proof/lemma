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
import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part4
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

instance (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, twist_discriminant, isUnit_iff_ne_zero]
  apply mul_ne_zero (pow_ne_zero 6 (cubicRat_ne_zero W))
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  simpa using RatFunc.C_injective.ne hΔ

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
