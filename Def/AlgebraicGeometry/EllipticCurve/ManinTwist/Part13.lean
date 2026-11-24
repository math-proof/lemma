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
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part12
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

def affineSolutionsEquivSquareFibers (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, squareFiber W x where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (equation_iff_square W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (equation_iff_square W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
