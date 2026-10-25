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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part13
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

lemma minusOneQuotient_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W / minusOneGCD W).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hmulB :
      minusOneGCD W * (minusOneNumerator W / minusOneGCD W) =
        minusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivB
  have hquotB : minusOneNumerator W / minusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulB
    exact hB hmulB.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotB
  rw [hmulB, minusOneNumerator_natDegree hchar W hcard] at hdegreeProduct
  have hdegreeG := minusOneGCD_natDegree_add_fiber_sum hchar W hcard
  omega

lemma num_natDegree_minusOneRat [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2)).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (frobeniusPolynomial : F[X]) 2]
  rw [natDegree_num_div _ _ (pow_ne_zero 2 frobeniusPolynomial_ne_zero)]
  exact minusOneQuotient_natDegree hchar W hcard

lemma d_neg_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (hcard : Nat.card F ≠ 3) :
    d hchar W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := point_neg_one_eq_some hchar W
  unfold d
  rw [hpoint]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))))).natDegree = _
  rw [paperX_negPZero_add_Q hchar W]
  rw [num_natDegree_minusOneRat hchar W hcard]
  exact (pointCount_eq_fiber_sum W).symm

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
