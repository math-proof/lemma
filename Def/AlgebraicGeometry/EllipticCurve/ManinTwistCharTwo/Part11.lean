module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Manin's elementary proof in characteristic two

This file packages the ordinary and supersingular normal-form cases, following
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).
-/
namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

noncomputable section

open Polynomial

open scoped CharTwo

open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

universe u

variable {F : Type u} [Field F]

def affineSolutionsEquivOrdinaryFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber x ((ordinaryH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (ordinaryEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (ordinaryEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
