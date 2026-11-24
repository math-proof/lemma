module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Def.AlgebraicGeometry.EllipticCurve.ManinTwist
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/
namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma cubic_ne_zero (W : WeierstrassCurve F) : cubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff 3) h
  simp [cubic] at hcoeff

lemma cubic_degree (W : WeierstrassCurve F) : (cubic W).degree = 3 := by
  rw [degree_eq_natDegree (cubic_ne_zero W), cubic_natDegree]
  norm_num

lemma cubic_discr (W : WeierstrassCurve F) :
    (cubic W).discr =
      W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ -
        27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three (cubic_degree W)]
  norm_num [cubic]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
