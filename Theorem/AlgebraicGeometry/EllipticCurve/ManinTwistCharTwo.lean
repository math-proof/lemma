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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
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

lemma frobeniusTail_identity [CharP F 2] (h k : F[X]) (e : ℕ) :
    frobeniusTail h k e ^ 2 + k ^ (2 ^ e) * frobeniusTail h k e =
      h ^ (2 ^ e) + k ^ (2 * (2 ^ e - 1)) * h := by
  induction e with
  | zero => simp [frobeniusTail, CharTwo.add_self_eq_zero]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hsq := congrArg (fun p : F[X] ↦ p ^ 2) ih
      rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow, mul_pow] at hsq
      have hB4 : (frobeniusTail h k e ^ 2) ^ 2 = frobeniusTail h k e ^ 4 := by
        ring
      have hk2q : (k ^ (2 ^ e)) ^ 2 = k ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hh2q : (h ^ (2 ^ e)) ^ 2 = h ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hk4q : (k ^ (2 * (2 ^ e - 1))) ^ 2 = k ^ (4 * q - 4) := by
        rw [← pow_mul]
        congr 1
        dsimp [q]
        omega
      rw [hB4, hk2q, hh2q, hk4q] at hsq
      have hsq' :
          frobeniusTail h k e ^ 4 + k ^ (2 * q) * frobeniusTail h k e ^ 2 =
            h ^ (2 * q) + k ^ (4 * q - 4) * h ^ 2 := hsq
      rw [frobeniusTail, hq, CharTwo.add_sq]
      rw [show (k ^ (2 * q - 2) * h) ^ 2 =
        k ^ (4 * q - 4) * h ^ 2 by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega]
      rw [mul_add]
      rw [show k ^ (2 * q) * (k ^ (2 * q - 2) * h) =
        k ^ (4 * q - 2) * h by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega]
      rw [show h ^ (2 * q) = (h ^ q) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [show k ^ (2 * (2 * q - 1)) = k ^ (4 * q - 2) by
        congr 1
        omega]
      have hcancel :
          k ^ (4 * q - 4) * h ^ 2 + k ^ (4 * q - 4) * h ^ 2 = 0 :=
        CharTwo.add_self_eq_zero _
      linear_combination hsq' + hcancel

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
