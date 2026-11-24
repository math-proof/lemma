module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Lemma.Scheme.EllipticCurve.VariableChangePoint
public import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
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
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part13
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

def symmetricInput (f g : F[X]) : Fin 3 → F[X] :=
  ![X * f, X * g + f, g]

def symmetricOutput (W : WeierstrassCurve F) (f g : F[X]) :
    Fin 3 → F[X] :=
  fun i ↦ MvPolynomial.eval (symmetricInput f g) ((W.map C).addSubMap i)

def additionCommon (W : WeierstrassCurve F) (r : RatFunc F) : RatFunc F :=
  (RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
    2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)

def symmetricFirstRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  (RatFunc.X * r - RatFunc.C W.a₄) ^ 2 -
    4 * RatFunc.C W.a₆ * (RatFunc.X + RatFunc.C W.a₂ + r)

def symmetricSecondRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  2 * additionCommon W r

def symmetricDenominatorRat (r : RatFunc F) : RatFunc F :=
  (RatFunc.X - r) ^ 2

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
