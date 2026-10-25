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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part8
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

lemma paper_coordinates_equation (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y) :
    cubicRat W * paperY W y ^ 2 =
      paperX W x ^ 3 + RatFunc.C W.a₂ * paperX W x ^ 2 +
        RatFunc.C W.a₄ * paperX W x + RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [twist] at heq
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W]
  linear_combination heq

lemma intDegree_cubicRat_mul_paperY_le_one
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : (paperX W x).intDegree ≤ 0) :
    (cubicRat W * paperY W y).intDegree ≤ 1 := by
  let r := paperX W x
  let s := paperY W y
  change (cubicRat W * s).intDegree ≤ 1
  by_cases hs0 : s = 0
  · simp [s, hs0]
  have hA : cubicRat W ≠ 0 := cubicRat_ne_zero W
  have hAs : cubicRat W * s ≠ 0 := mul_ne_zero hA hs0
  have heq := paper_coordinates_equation W hxy
  change cubicRat W * s ^ 2 =
    r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r + RatFunc.C W.a₆ at heq
  have hr : r.intDegree ≤ 0 := hx
  have hcubic := intDegree_cubic_paperX_le_zero W hr
  have hproduct :
      (cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆)).intDegree ≤ 3 := by
    have := intDegree_mul_le_of_le (x := cubicRat W)
      (y := r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) (m := 3) (n := 0) (by norm_num)
      (by rw [intDegree_cubicRat]) hcubic
    norm_num at this ⊢
    exact this
  have hsquare : (cubicRat W * s) ^ 2 =
      cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  rw [← hsquare, intDegree_pow hAs] at hproduct
  norm_num at hproduct ⊢
  omega

lemma paperX_Q_coordinate (W : WeierstrassCurve F) :
    paperX W (cubicRat W * RatFunc.X) = RatFunc.X := by
  unfold paperX
  field_simp [cubicRat_ne_zero W]

lemma paperX_addX_Q_eq (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      cubicRat W *
          ((paperY W y - 1) / (paperX W x - RatFunc.X)) ^ 2 -
        RatFunc.C W.a₂ - paperX W x - RatFunc.X := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, twist]
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W, hx]
  ring

lemma paperX_addX_Q_canceled (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      ((RatFunc.X + paperX W x) *
          (RatFunc.C W.a₄ + RatFunc.X * paperX W x) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * paperX W x + RatFunc.C W.a₆) -
        2 * cubicRat W * paperY W y) /
      (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_eq W hx]
  have heq := paper_coordinates_equation W hxy
  have hden : paperX W x - RatFunc.X ≠ 0 := by
    intro h
    apply hx
    have hpaper : paperX W x = RatFunc.X := sub_eq_zero.mp h
    unfold paperX at hpaper
    calc
      x = RatFunc.X * cubicRat W := (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
      _ = cubicRat W * RatFunc.X := mul_comm _ _
  rw [cubicRat_eq W] at heq ⊢
  field_simp [hden, sub_ne_zero.mpr (Ne.symm <| sub_ne_zero.mp hden)]
  linear_combination (paperX W x - RatFunc.X) ^ 2 * heq

set_option maxHeartbeats 500000 in

lemma intDegree_paperX_addX_Q_le_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X)
    (hdegree : (paperX W x).intDegree ≤ 0) :
    (paperX W
      ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
        ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
          (cubicRat W ^ 2)))).intDegree ≤ 0 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  exact intDegree_canceled_expression_le_zero
    (cubicRat W) (paperX W x) (paperY W y) W.a₂ W.a₄ W.a₆ hdegree
      (intDegree_cubicRat_mul_paperY_le_one W hxy hdegree)

lemma badAtInfinity_add_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P + Q W) := by
  cases P with
  | zero => simp [badAtInfinity] at hP
  | some x y hxy =>
      change (paperX W x).intDegree ≤ 0 at hP
      have hx : x ≠ cubicRat W * RatFunc.X := by
        intro hx
        have hpaper : paperX W x = RatFunc.X := by
          rw [hx, paperX_Q_coordinate]
        rw [hpaper] at hP
        norm_num at hP
      have hvertical :
          ¬(x = cubicRat W * RatFunc.X ∧
            y = (twist W).toAffine.negY (cubicRat W * RatFunc.X)
              (cubicRat W ^ 2)) := fun h ↦ hx h.1
      rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) _ from rfl]
      rw [WeierstrassCurve.Affine.Point.add_some hvertical]
      exact intDegree_paperX_addX_Q_le_zero W hxy hx hP

lemma badAtInfinity_sub_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P - Q W) := by
  have hnegP : badAtInfinity W (-P) := (badAtInfinity_neg W P).mpr hP
  have hadd := badAtInfinity_add_Q W hnegP
  rw [show P - Q W = -(-P + Q W) by abel]
  exact (badAtInfinity_neg W (-P + Q W)).mpr hadd

lemma badAtInfinity_add_Q_iff (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (P + Q W) ↔ badAtInfinity W P := by
  refine ⟨fun h ↦ ?_, badAtInfinity_add_Q W⟩
  have hsub := badAtInfinity_sub_Q W h
  simpa using hsub

lemma paperX_pZeroX [Finite F] (W : WeierstrassCurve F) :
    paperX W (pZeroX W) = RatFunc.X ^ Nat.card F := by
  unfold paperX pZeroX
  field_simp [cubicRat_ne_zero W]

lemma pZero_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ¬badAtInfinity W (P₀ hchar W) := by
  intro hbad
  change (paperX W (pZeroX W)).intDegree ≤ 0 at hbad
  rw [paperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

lemma point_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    ¬badAtInfinity W (point hchar W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [point] using pZero_not_badAtInfinity hchar W
  · intro k _ hk hbad
    apply hk
    apply (badAtInfinity_add_Q_iff W (point hchar W k)).mp
    rw [← point_add_one hchar W k]
    exact hbad
  · intro k _ hk hbad
    apply hk
    have hstep := point_add_one hchar W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (badAtInfinity_add_Q_iff W (point hchar W (k - 1))).mpr hbad

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
