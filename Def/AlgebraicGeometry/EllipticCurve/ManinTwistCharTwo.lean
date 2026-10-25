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

def quadraticDegree (q : ℕ) (a n : ℤ) : ℤ :=
  n ^ 2 + a * n + q

def nonnegativeQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ quadraticDegree q a n)
    (hnoAdjacent : ∀ n, quadraticDegree q a n = 0 →
      quadraticDegree q a (n + 1) = 0 → False) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic q N a ha
    (by simpa only [quadraticDegree] using hnonneg)
    (by simpa only [quadraticDegree] using hnoAdjacent)

def positiveQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ)) (hpos : ∀ n, 0 < quadraticDegree q a n) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  nonnegativeQuadraticDegreeData q N a ha (fun n ↦ (hpos n).le)
    (fun n hn _ ↦ by nlinarith [hpos n])

def frobeniusTail (h k : F[X]) : ℕ → F[X]
  | 0 => 0
  | e + 1 => frobeniusTail h k e ^ 2 + k ^ (2 ^ (e + 1) - 2) * h

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
