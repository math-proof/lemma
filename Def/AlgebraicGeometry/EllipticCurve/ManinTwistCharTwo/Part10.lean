/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Instance.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part3
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

def ordinaryPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    (ordinaryTwist W).toAffine.Point := ordinaryPZero W + n • ordinaryQ W

def ordinaryPaperX (x : RatFunc F) : RatFunc F := x / RatFunc.X ^ 2

def ordinaryPaperY (y : RatFunc F) : RatFunc F := y / RatFunc.X ^ 3

def ordinaryBadAtInfinity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (ordinaryPaperX x).intDegree ≤ 0

def ordinaryD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) : ℕ :=
  match ordinaryPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (ordinaryPaperX x)).natDegree

def ordinaryMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
