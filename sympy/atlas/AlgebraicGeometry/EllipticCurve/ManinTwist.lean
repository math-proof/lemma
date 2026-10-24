/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import sympy.atlas.AlgebraicGeometry.EllipticCurve.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import sympy.atlas.AlgebraicGeometry.EllipticCurve.PointCount
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

/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/

open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

private def cubic (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

private lemma cubic_ne_zero (W : WeierstrassCurve F) : cubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff 3) h
  simp [cubic] at hcoeff

private lemma cubic_degree (W : WeierstrassCurve F) : (cubic W).degree = 3 := by
  rw [degree_eq_natDegree (cubic_ne_zero W), cubic_natDegree]
  norm_num

private lemma cubic_discr (W : WeierstrassCurve F) :
    (cubic W).discr =
      W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ -
        27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three (cubic_degree W)]
  norm_num [cubic]

private def duplicationNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 - C (2 * W.a₄) * X ^ 2 - C (8 * W.a₆) * X +
    C (W.a₄ ^ 2 - 4 * W.a₂ * W.a₆)

private lemma delta_eq_sixteen_mul_cubic_discr
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    W.Δ = 16 * (cubic W).discr := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, cubic_discr]
  ring

private lemma cubic_discr_ne_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).discr ≠ 0 := by
  intro h
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  apply hΔ
  rw [delta_eq_sixteen_mul_cubic_discr, h, mul_zero]

private lemma cubic_separable (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).Separable := by
  rw [Polynomial.separable_def]
  have hdegDeriv : (cubic W).derivative.natDegree ≤ 2 := by
    simpa [cubic_natDegree] using Polynomial.natDegree_derivative_le (cubic W)
  have hres :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 =
        -(cubic W).discr := by
    have h := Polynomial.resultant_deriv (f := cubic W) (by
      rw [cubic_degree]
      norm_num)
    rw [cubic_natDegree] at h
    norm_num [cubic_monic W] at h
    exact h
  have hresne :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 ≠ 0 := by
    rw [hres]
    exact neg_ne_zero.mpr (cubic_discr_ne_zero W)
  obtain ⟨p, q, _, _, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (cubic W) (cubic W).derivative (m := 3) (n := 2)
        (cubic_natDegree W).le hdegDeriv (by omega)
  refine ⟨C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p,
    C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q, ?_⟩
  calc
    (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p) *
          cubic W +
        (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q) *
          (cubic W).derivative =
        C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ *
          (cubic W * p + (cubic W).derivative * q) := by ring
    _ = 1 := by rw [hpq, ← map_mul, inv_mul_cancel₀ hresne, map_one]

private lemma isCoprime_cubic_duplicationNumerator
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    IsCoprime (cubic W) (duplicationNumerator W) := by
  have hc : IsCoprime (cubic W) ((cubic W).derivative ^ 2) :=
    ((Polynomial.separable_def (cubic W)).mp (cubic_separable W)).pow_right
  obtain ⟨u, v, huv⟩ := hc
  let k : F[X] := C 4 * (C W.a₂ + C 2 * X)
  refine ⟨u + v * k, v, ?_⟩
  rw [duplicationNumerator_eq]
  change (u + v * k) * cubic W +
    v * ((cubic W).derivative ^ 2 - k * cubic W) = 1
  calc
    (u + v * k) * cubic W +
        v * ((cubic W).derivative ^ 2 - k * cubic W) =
      u * cubic W + v * (cubic W).derivative ^ 2 := by ring
    _ = 1 := huv

private def cubicRat (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (cubic W)

private lemma cubicRat_ne_zero (W : WeierstrassCurve F) : cubicRat W ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (cubic_ne_zero W)

private lemma cubicRat_eq (W : WeierstrassCurve F) :
    cubicRat W = RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆ := by
  simp [cubicRat, cubic, RatFunc.algebraMap_X]

private def twist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, RatFunc.C W.a₂ * cubicRat W, 0, RatFunc.C W.a₄ * cubicRat W ^ 2,
    RatFunc.C W.a₆ * cubicRat W ^ 3⟩

private instance (W : WeierstrassCurve F) : (twist W).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

private lemma twist_discriminant (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).Δ = cubicRat W ^ 6 * RatFunc.C W.Δ := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF,
    WeierstrassCurve.Δ_of_isCharNeTwoNF]
  simp only [twist, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

private instance (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, twist_discriminant, isUnit_iff_ne_zero]
  apply mul_ne_zero (pow_ne_zero 6 (cubicRat_ne_zero W))
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  simpa using RatFunc.C_injective.ne hΔ

private lemma q_equation (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist]
  rw [cubicRat_eq]
  ring

private def Q (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (q_equation W)

private lemma card_odd [Finite F] (hchar : ringChar F ≠ 2) : Odd (Nat.card F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  obtain ⟨p, hpF, n, hp, hcard⟩ := @FiniteField.card' F _ fintypeF
  let _ : CharP F p := hpF
  have hpne : p ≠ 2 := by
    intro h
    apply hchar
    rw [ringChar.eq F p, h]
  rw [hcard]
  exact hp.odd_of_ne_two hpne |>.pow

private lemma twice_half_card_add_three [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 3) / 2) = Nat.card F + 3 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma aeval_cubic_X_pow_card [Finite F] (W : WeierstrassCurve F) :
    aeval (RatFunc.X ^ Nat.card F) (cubic W) = cubicRat W ^ Nat.card F := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  calc
    aeval (RatFunc.X ^ Fintype.card F) (cubic W) =
        aeval RatFunc.X (Polynomial.expand F (Fintype.card F) (cubic W)) := by
      rw [Polynomial.expand_aeval]
    _ = aeval RatFunc.X (cubic W ^ Fintype.card F) := by
      rw [FiniteField.Polynomial.expand_card]
    _ = cubicRat W ^ Fintype.card F := by
      simp [cubicRat, RatFunc.aeval_X_left_eq_algebraMap]

private def pZeroX [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W * RatFunc.X ^ Nat.card F

private def pZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W ^ ((Nat.card F + 3) / 2)

private lemma pZero_equation [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation (pZeroX W) (pZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist, pZeroX, pZeroY]
  have hcubic := aeval_cubic_X_pow_card W
  simp only [cubic, map_add, map_mul, map_pow, aeval_X, aeval_C] at hcubic
  rw [← pow_mul]
  rw [show (Nat.card F + 3) / 2 * 2 = Nat.card F + 3 by
    rw [mul_comm, twice_half_card_add_three hchar]]
  simp only [zero_mul, add_zero]
  calc
    cubicRat W ^ (Nat.card F + 3) =
        cubicRat W ^ 3 * cubicRat W ^ Nat.card F := by
      rw [pow_add]
      ring
    _ = cubicRat W ^ 3 *
        ((RatFunc.X ^ Nat.card F) ^ 3 +
          algebraMap F (RatFunc F) W.a₂ * (RatFunc.X ^ Nat.card F) ^ 2 +
          algebraMap F (RatFunc F) W.a₄ * RatFunc.X ^ Nat.card F +
          algebraMap F (RatFunc F) W.a₆) := by
      rw [← hcubic]
    _ = _ := by
      simp only [RatFunc.algebraMap_eq_C]
      ring

private def P₀ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (pZero_equation hchar W)

private local instance : DecidableEq F := Classical.decEq F

private def point [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    (twist W).toAffine.Point :=
  P₀ hchar W + n • Q W

private def paperX (W : WeierstrassCurve F) (x : RatFunc F) : RatFunc F :=
  x / cubicRat W

private def paperY (W : WeierstrassCurve F) (y : RatFunc F) : RatFunc F :=
  y / cubicRat W ^ 2

private def badAtInfinity (W : WeierstrassCurve F) :
    (twist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (paperX W x).intDegree ≤ 0

private lemma paper_coordinates_equation (W : WeierstrassCurve F)
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

private lemma intDegree_cubicRat_mul_paperY_le_one
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

private lemma paperX_Q_coordinate (W : WeierstrassCurve F) :
    paperX W (cubicRat W * RatFunc.X) = RatFunc.X := by
  unfold paperX
  field_simp [cubicRat_ne_zero W]

private lemma paperX_addX_Q_eq (W : WeierstrassCurve F)
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

private lemma paperX_addX_Q_canceled (W : WeierstrassCurve F)
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

private lemma intDegree_paperX_addX_Q_le_zero
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

private lemma badAtInfinity_add_Q (W : WeierstrassCurve F)
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

private lemma badAtInfinity_sub_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P - Q W) := by
  have hnegP : badAtInfinity W (-P) := (badAtInfinity_neg W P).mpr hP
  have hadd := badAtInfinity_add_Q W hnegP
  rw [show P - Q W = -(-P + Q W) by abel]
  exact (badAtInfinity_neg W (-P + Q W)).mpr hadd

private lemma badAtInfinity_add_Q_iff (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (P + Q W) ↔ badAtInfinity W P := by
  refine ⟨fun h ↦ ?_, badAtInfinity_add_Q W⟩
  have hsub := badAtInfinity_sub_Q W h
  simpa using hsub

private lemma paperX_pZeroX [Finite F] (W : WeierstrassCurve F) :
    paperX W (pZeroX W) = RatFunc.X ^ Nat.card F := by
  unfold paperX pZeroX
  field_simp [cubicRat_ne_zero W]

private lemma pZero_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ¬badAtInfinity W (P₀ hchar W) := by
  intro hbad
  change (paperX W (pZeroX W)).intDegree ≤ 0 at hbad
  rw [paperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

private lemma point_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
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

private def d [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) : ℕ :=
  match point hchar W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (x / cubicRat W)).natDegree

private lemma num_natDegree_gt_denom_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    (hn : point hchar W n = .some x y hxy) :
    (RatFunc.denom (x / cubicRat W)).natDegree <
      (RatFunc.num (x / cubicRat W)).natDegree := by
  have hnotBad := point_not_badAtInfinity hchar W n
  have hnotLe : ¬(paperX W x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (paperX W x).intDegree := lt_of_not_ge hnotLe
  unfold paperX RatFunc.intDegree at hpos
  omega

private lemma d_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    d hchar W 0 = Nat.card F := by
  rw [d, point]
  simp only [zero_zsmul, add_zero, P₀, WeierstrassCurve.Affine.Point.mk]
  have hx : pZeroX W / cubicRat W = RatFunc.X ^ Nat.card F := by
    rw [div_eq_iff (cubicRat_ne_zero W)]
    simp only [pZeroX]
    ring
  rw [hx]
  change
    (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
      Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma d_eq_zero_iff_point_eq_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W n = 0 ↔ point hchar W n = 0 := by
  cases hp : point hchar W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [d, hp]
  | some x y hxy =>
      have hdeg := num_natDegree_gt_denom_natDegree hchar W hp
      constructor
      · intro hd
        simp only [d, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma noAdjacentZeros [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∀ n, d hchar W n = 0 → d hchar W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (d_eq_zero_iff_point_eq_zero hchar W n).mp hn
  have hp1 := (d_eq_zero_iff_point_eq_zero hchar W (n + 1)).mp hn1
  apply Q_ne_zero W
  have hs := point_add_one hchar W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private def frobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private def eulerPolynomial [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W ^ ((Nat.card F - 1) / 2)

private def minusOneNumerator [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W * (eulerPolynomial W + 1) ^ 2 -
    (C W.a₂ + X ^ Nat.card F + X) * frobeniusPolynomial ^ 2

private lemma card_gt_three [Finite F] (hchar : ringChar F ≠ 2)
    (hcard : Nat.card F ≠ 3) : 3 < Nat.card F := by
  obtain ⟨k, hk⟩ := card_odd hchar
  have hlarge := Finite.one_lt_card (α := F)
  omega

private lemma twice_half_card_sub_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma twice_half_card_add_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 1) / 2) = Nat.card F + 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma minusOneNumerator_eq [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    minusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
        C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        C W.a₄ * X ^ Nat.card F +
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) + C W.a₄ * X +
        C (2 * W.a₆) := by
  have heven := twice_half_card_sub_one (F := F) hchar
  have hpower :
      cubic W * eulerPolynomial W ^ 2 = cubic W ^ Nat.card F := by
    rw [eulerPolynomial, ← pow_mul]
    rw [show (Nat.card F - 1) / 2 * 2 = Nat.card F - 1 by
      rw [mul_comm, heven]]
    calc
      cubic W * cubic W ^ (Nat.card F - 1) =
          cubic W ^ (Nat.card F - 1 + 1) := (pow_succ' _ _).symm
      _ = cubic W ^ Nat.card F := by
        congr
        have hpos := Nat.card_pos (α := F)
        omega
  have hmiddle :
      cubic W * (C 2 * eulerPolynomial W) =
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) := by
    rw [eulerPolynomial]
    have hadd : (Nat.card F - 1) / 2 + 1 = (Nat.card F + 1) / 2 := by
      obtain ⟨k, hk⟩ := card_odd hchar
      omega
    rw [show cubic W * (C 2 * cubic W ^ ((Nat.card F - 1) / 2)) =
      C 2 * cubic W ^ ((Nat.card F - 1) / 2 + 1) by ring]
    rw [hadd]
  unfold minusOneNumerator
  rw [show (eulerPolynomial W + 1) ^ 2 =
    eulerPolynomial W ^ 2 + C 2 * eulerPolynomial W + 1 by
      rw [Polynomial.C_ofNat]
      ring]
  rw [mul_add, mul_add, hpower, hmiddle, mul_one, cubic_pow_card]
  unfold frobeniusPolynomial
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma minusOneNumerator_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  have hq := card_gt_three (F := F) hchar hcard
  have hhalf := twice_half_card_add_one (F := F) hchar
  let remainder : F[X] :=
    X ^ (Nat.card F + 2) +
      (C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        (C W.a₄ * X ^ Nat.card F +
          (C 2 * cubic W ^ ((Nat.card F + 1) / 2) +
            (C W.a₄ * X + C (2 * W.a₆)))))
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    apply natDegree_add_le_of_le
    · rw [Polynomial.natDegree_X_pow]
      omega
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · calc
        (C 2 * cubic W ^ ((Nat.card F + 1) / 2)).natDegree ≤
            (cubic W ^ ((Nat.card F + 1) / 2)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ = (Nat.card F + 1) / 2 * 3 := by
          rw [Polynomial.natDegree_pow, cubic_natDegree]
        _ ≤ 2 * Nat.card F := by omega
    apply natDegree_add_le_of_le
    · simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le W.a₄ 1).trans (by omega)
    · rw [Polynomial.natDegree_C]
      omega
  have heq :
      minusOneNumerator W = X ^ (2 * Nat.card F + 1) + remainder := by
    rw [minusOneNumerator_eq hchar]
    dsimp only [remainder]
    ring
  rw [heq]
  have hlt :
      remainder.natDegree < (X ^ (2 * Nat.card F + 1) : F[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    omega
  calc
    (X ^ (2 * Nat.card F + 1) + remainder).natDegree =
        (X ^ (2 * Nat.card F + 1) : F[X]).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
    _ = 2 * Nat.card F + 1 := Polynomial.natDegree_X_pow _

private lemma pZeroX_ne_qX [Finite F] (W : WeierstrassCurve F) :
    pZeroX W ≠ cubicRat W * RatFunc.X := by
  intro h
  have hpow : RatFunc.X ^ Nat.card F = RatFunc.X :=
    mul_left_cancel₀ (cubicRat_ne_zero W) h
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at hdegree
  simp only [mul_one] at hdegree
  have hcard := Finite.one_lt_card (α := F)
  omega

private lemma paperY_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W (pZeroY W) = cubicRat W ^ ((Nat.card F - 1) / 2) := by
  have hexponent :
      (Nat.card F + 3) / 2 = (Nat.card F - 1) / 2 + 2 := by
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  unfold paperY pZeroY
  rw [hexponent, pow_add]
  field_simp [cubicRat_ne_zero W]

private lemma cubic_mul_eulerPolynomial [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    cubic W * eulerPolynomial W = cubic W ^ ((Nat.card F + 1) / 2) := by
  unfold eulerPolynomial
  rw [show cubic W * cubic W ^ ((Nat.card F - 1) / 2) =
    cubic W ^ ((Nat.card F - 1) / 2 + 1) by
      exact (pow_succ' _ _).symm]
  congr 1
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma minusOneNumerator_canceled_eq [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    minusOneNumerator W =
      (X + X ^ Nat.card F) * (C W.a₄ + X * X ^ Nat.card F) +
        C 2 * (C W.a₂ * X * X ^ Nat.card F + C W.a₆) +
        C 2 * cubic W * eulerPolynomial W := by
  rw [minusOneNumerator_eq hchar]
  rw [show C 2 * cubic W * eulerPolynomial W =
    C 2 * (cubic W * eulerPolynomial W) by ring]
  rw [cubic_mul_eulerPolynomial hchar]
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma paperY_neg_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) =
      -(cubicRat W ^ ((Nat.card F - 1) / 2)) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  rw [show paperY W (-pZeroY W) = -paperY W (pZeroY W) by
    unfold paperY
    exact neg_div _ _]
  rw [paperY_pZeroY hchar W]

private lemma algebraMap_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    algebraMap F[X] (RatFunc F) (minusOneNumerator W) =
      (RatFunc.X + RatFunc.X ^ Nat.card F) *
          (RatFunc.C W.a₄ + RatFunc.X * RatFunc.X ^ Nat.card F) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * RatFunc.X ^ Nat.card F +
          RatFunc.C W.a₆) +
        2 * cubicRat W * cubicRat W ^ ((Nat.card F - 1) / 2) := by
  rw [minusOneNumerator_canceled_eq hchar]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, cubicRat, eulerPolynomial]

private lemma paperX_negPZero_add_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2 := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  rw [paperX_addX_Q_canceled W hneg (pZeroX_ne_qX W)]
  rw [paperX_pZeroX, paperY_neg_pZeroY hchar W]
  rw [algebraMap_minusOneNumerator hchar, algebraMap_frobeniusPolynomial]
  ring

private lemma point_neg_one_eq_some [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∃ y hxy, point hchar W (-1) =
      .some
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) y hxy := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -P₀ hchar W = .some (pZeroX W)
        ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) hneg := by
    rw [show P₀ hchar W = .some (pZeroX W) (pZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) (pZeroX_ne_qX W)
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W))
  rw [← hnegP, ← show Q W = .some (cubicRat W * RatFunc.X)
    (cubicRat W ^ 2) _ from rfl] at hadd
  have hpoint : point hchar W (-1) = -(-P₀ hchar W + Q W) := by
    unfold point
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private def squareFiber (W : WeierstrassCurve F) (x : F) :=
  {y : F // y ^ 2 = (cubic W).eval x}

private instance squareFiberFinite [Finite F] (W : WeierstrassCurve F)
    (x : F) : Finite (squareFiber W x) := by
  unfold squareFiber
  infer_instance

private lemma eval_eulerPolynomial [Fintype F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) (x : F) :
    (eulerPolynomial W).eval x =
      ((quadraticChar F) ((cubic W).eval x) : F) := by
  have hhalf :
      Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  have hcriterion :=
    quadraticChar_eq_pow_of_char_ne_two' hchar ((cubic W).eval x)
  rw [hhalf] at hcriterion
  unfold eulerPolynomial
  rw [eval_pow, Nat.card_eq_fintype_card]
  exact hcriterion.symm

private lemma eval_eulerPolynomial_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (eulerPolynomial W).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar, hzero]
  simp

private lemma eval_eulerPolynomial_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [(quadraticChar_one_iff_isSquare hzero).mpr hsquare]
  simp

private lemma eval_eulerPolynomial_eq_neg_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = -1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsquare]
  simp

private lemma eval_derivative_minusOneNumerator_of_cubic_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (minusOneNumerator W).derivative.eval x = (cubic W).derivative.eval x := by
  have heuler := eval_eulerPolynomial_eq_zero hchar W x hzero
  have hfrobenius := eval_frobeniusPolynomial (F := F) x
  unfold minusOneNumerator
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add,
    derivative_one, eval_sub, eval_add, eval_mul, eval_pow, eval_one]
  rw [hzero, heuler, hfrobenius]
  ring

private lemma eval_derivative_cubic_ne_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (x : F) (hzero : (cubic W).eval x = 0) :
    (cubic W).derivative.eval x ≠ 0 := by
  intro hderivative
  obtain ⟨u, v, huv⟩ :=
    (Polynomial.separable_def (cubic W)).mp (cubic_separable W)
  have heval := congrArg (Polynomial.eval x) huv
  simp only [eval_add, eval_mul, eval_one] at heval
  rw [hzero, hderivative] at heval
  simp at heval

private lemma minusOneNumerator_ne_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) : minusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := minusOneNumerator_natDegree hchar W hcard
  rw [hzero] at hdegree
  simp at hdegree

private lemma rootMultiplicity_minusOneNumerator_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hroot : (minusOneNumerator W).IsRoot x := by
    change (minusOneNumerator W).eval x = 0
    rw [eval_minusOneNumerator, hzero]
    ring
  have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneNumerator W) := by
    rw [Polynomial.le_rootMultiplicity_iff hB]
    simpa using (Polynomial.dvd_iff_isRoot.mpr hroot)
  have hupper : Polynomial.rootMultiplicity x (minusOneNumerator W) ≤ 1 := by
    rw [Polynomial.rootMultiplicity_le_iff hB]
    intro hsquare
    have hderivative := eval_derivative_eq_zero_of_sq_dvd hsquare
    rw [eval_derivative_minusOneNumerator_of_cubic_eq_zero hchar W x hzero]
      at hderivative
    exact eval_derivative_cubic_ne_zero W x hzero hderivative
  omega

private lemma rootMultiplicity_minusOneNumerator_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heuler := eval_eulerPolynomial_eq_one hchar W x hzero hsquare
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hsum : (1 + 1 : F) ≠ 0 := by
    intro h
    apply htwo
    norm_num at h ⊢
    exact h
  have heval : (minusOneNumerator W).eval x ≠ 0 := by
    rw [eval_minusOneNumerator, heuler]
    exact mul_ne_zero hzero (pow_ne_zero 2 hsum)
  exact heval hroot

private lemma sq_X_sub_C_dvd_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (X - C x) ^ 2 ∣ minusOneNumerator W := by
  have heuler := eval_eulerPolynomial_eq_neg_one hchar W x hsquare
  have heulerRoot : (eulerPolynomial W + 1).IsRoot x := by
    simp only [IsRoot, eval_add, eval_one, heuler]
    ring
  have hfrobeniusRoot : (frobeniusPolynomial : F[X]).IsRoot x :=
    eval_frobeniusPolynomial x
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr heulerRoot
  obtain ⟨v, hv⟩ := Polynomial.dvd_iff_isRoot.mpr hfrobeniusRoot
  refine ⟨cubic W * u ^ 2 - (C W.a₂ + X ^ Nat.card F + X) * v ^ 2, ?_⟩
  unfold minusOneNumerator
  rw [hu, hv]
  ring

private def minusOneGCD [Finite F] (W : WeierstrassCurve F) : F[X] :=
  gcd (minusOneNumerator W) (frobeniusPolynomial ^ 2)

private lemma count_roots_minusOneGCD [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) :
    Multiset.count x (minusOneGCD W).roots =
      2 - Nat.card (squareFiber W x) := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (frobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_frobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣ (frobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hzero : (cubic W).eval x = 0
  · have hlinearB : X - C x ∣ minusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (minusOneNumerator W).eval x = 0
      rw [eval_minusOneNumerator, hzero]
      ring
    have hlinearL' : X - C x ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
      exact hlinearL.trans ⟨frobeniusPolynomial, by ring⟩
    have hcommon : X - C x ∣ minusOneGCD W := by
      unfold minusOneGCD
      exact dvd_gcd hlinearB hlinearL'
    have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity x (minusOneGCD W) ≤
            Polynomial.rootMultiplicity x (minusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
        _ = 1 := rootMultiplicity_minusOneNumerator_eq_one
          hchar W hcard x hzero
    have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      squareFiber_natCard_eq_one W x hzero]
  · by_cases hsquare : IsSquare ((cubic W).eval x)
    · have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x (minusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
          _ = 0 := rootMultiplicity_minusOneNumerator_eq_zero
            hchar W x hzero hsquare
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_two hchar W x hzero hsquare]
    · have hcommon : (X - C x) ^ 2 ∣ minusOneGCD W := by
        unfold minusOneGCD
        exact dvd_gcd
          (sq_X_sub_C_dvd_minusOneNumerator hchar W x hsquare) hlinearLsq
      have hlower : 2 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL :
          Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_frobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 2 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_zero W x hsquare]

private lemma minusOneGCD_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (minusOneGCD W).Splits :=
    (frobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (minusOneGCD W).roots) =
        (minusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (minusOneGCD W).roots) (by simp))
  calc
    (minusOneGCD W).natDegree = (minusOneGCD W).roots.card :=
      hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (minusOneGCD W).roots := hsum.symm
    _ = ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_minusOneGCD hchar W hcard x

private lemma minusOneGCD_natDegree_add_fiber_sum [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree + ∑ x : F, Nat.card (squareFiber W x) =
      2 * Nat.card F := by
  rw [minusOneGCD_natDegree hchar W hcard]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (squareFiber W x) +
        Nat.card (squareFiber W x))) = ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (squareFiber_natCard_le_two hchar W x)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma equation_iff_square (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = (cubic W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₃_of_isCharNeTwoNF, zero_mul]
  simp only [cubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  simp

private def affineSolutionsEquivSquareFibers (W : WeierstrassCurve F)
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

private lemma minusOneQuotient_natDegree [Fintype F]
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

private lemma num_natDegree_minusOneRat [Fintype F]
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

private lemma d_neg_one [Finite F] (hchar : ringChar F ≠ 2)
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

private def symmetricInput (f g : F[X]) : Fin 3 → F[X] :=
  ![X * f, X * g + f, g]

private def symmetricOutput (W : WeierstrassCurve F) (f g : F[X]) :
    Fin 3 → F[X] :=
  fun i ↦ MvPolynomial.eval (symmetricInput f g) ((W.map C).addSubMap i)

private def additionCommon (W : WeierstrassCurve F) (r : RatFunc F) : RatFunc F :=
  (RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
    2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)

private def symmetricFirstRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  (RatFunc.X * r - RatFunc.C W.a₄) ^ 2 -
    4 * RatFunc.C W.a₆ * (RatFunc.X + RatFunc.C W.a₂ + r)

private def symmetricSecondRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  2 * additionCommon W r

private def symmetricDenominatorRat (r : RatFunc F) : RatFunc F :=
  (RatFunc.X - r) ^ 2

private lemma addition_product_identity (W : WeierstrassCurve F)
    {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) :
    (additionCommon W r - 2 * cubicRat W * s) *
        (additionCommon W r + 2 * cubicRat W * s) =
      symmetricDenominatorRat r * symmetricFirstRat W r := by
  have hsquare :
      (cubicRat W * s) ^ 2 =
        cubicRat W *
          (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 +
            RatFunc.C W.a₄ * r + RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  have hproduct := product_formula
    (RatFunc.C W.a₂) (RatFunc.C W.a₄) (RatFunc.C W.a₆)
      RatFunc.X r 1
  rw [cubicRat_eq] at hsquare
  dsimp only at hproduct
  unfold additionCommon symmetricDenominatorRat symmetricFirstRat
  rw [cubicRat_eq W]
  calc
    _ = ((RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
          2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)) ^ 2 -
        4 * ((RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
          RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * s) ^ 2 := by ring
    _ = _ := by
      rw [hsquare]
      linear_combination hproduct

private lemma symmetricOutput_pair_product (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 *
        ((additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2) := by
  rw [symmetricOutput_zero_ratio]
  unfold symmetricDenominatorRat
  have hproduct := addition_product_identity W heq
  unfold symmetricDenominatorRat at hproduct
  field_simp [hdiff]
  linear_combination -hproduct

private lemma paperX_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) -
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  rfl

private lemma paperX_neg_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY x y) (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) +
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  rw [paperX_addX_Q_common W hneg hx]
  rw [paperY_negY]
  ring

private def addQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
      (cubicRat W ^ 2))

private def subQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
      ((twist W).toAffine.negY x y) (cubicRat W ^ 2))

private lemma X_sub_paperX_ne_zero (W : WeierstrassCurve F)
    {x : RatFunc F} (hx : x ≠ cubicRat W * RatFunc.X) :
    RatFunc.X - paperX W x ≠ 0 := by
  intro hzero
  apply hx
  have hpaper : paperX W x = RatFunc.X := by
    exact (sub_eq_zero.mp hzero).symm
  unfold paperX at hpaper
  calc
    x = RatFunc.X * cubicRat W :=
      (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
    _ = cubicRat W * RatFunc.X := by ring

private lemma Q_y_ne_negY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    cubicRat W ^ 2 ≠
      (twist W).toAffine.negY (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  intro hneg
  have htwoF := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have htwo : (2 : RatFunc F) ≠ 0 := by
    intro hzero
    apply htwoF
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  have hsum : (2 : RatFunc F) * cubicRat W ^ 2 = 0 := by
    linear_combination hneg
  rcases mul_eq_zero.mp hsum with htwoZero | hcubicZero
  · exact htwo htwoZero
  · exact cubicRat_ne_zero W (sq_eq_zero_iff.mp hcubicZero)

private lemma paperX_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2) (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W) := by
  have hnum :
      (cubicRat W * RatFunc.X) ^ 4 -
          (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) ^ 2 -
          2 * (twist W).toAffine.b₆ * (cubicRat W * RatFunc.X) -
          (twist W).toAffine.b₈ =
        cubicRat W ^ 4 *
          algebraMap F[X] (RatFunc F) (duplicationNumerator W) := by
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, twist]
    simp only [duplicationNumerator, map_add, map_sub, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    ring
  have hden :
      4 * (cubicRat W * RatFunc.X) ^ 3 +
          (twist W).toAffine.b₂ * (cubicRat W * RatFunc.X) ^ 2 +
          2 * (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) +
          (twist W).toAffine.b₆ =
        4 * cubicRat W ^ 4 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, twist]
    rw [cubicRat_eq W]
    ring
  have hfourRat : (4 : RatFunc F) ≠ 0 := by
    intro hzero
    apply four_ne_zero_of_ringChar_ne_two (F := F) hchar
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  rw [(twist W).toAffine.addX_self_of_Y_ne (q_equation W)
    (Q_y_ne_negY hchar W)]
  rw [hnum, hden]
  unfold paperX
  field_simp [cubicRat_ne_zero W, hfourRat]

private lemma num_natDegree_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W))).natDegree = 4 := by
  have hfour := four_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hCfour : C (4 : F) ≠ 0 := Polynomial.C_ne_zero.mpr hfour
  have hden : C (4 : F) * cubic W ≠ 0 :=
    mul_ne_zero hCfour (cubic_ne_zero W)
  have hcopFour : IsCoprime (duplicationNumerator W) (C (4 : F)) := by
    refine ⟨0, C (4 : F)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hfour, C_1]
  have hcop :
      IsCoprime (duplicationNumerator W) (C (4 : F) * cubic W) :=
    hcopFour.mul_right (isCoprime_cubic_duplicationNumerator W).symm
  have hmapDen :
      (4 : RatFunc F) * cubicRat W =
        algebraMap F[X] (RatFunc F) (C (4 : F) * cubic W) := by
    rw [map_mul, RatFunc.algebraMap_C]
    change (4 : RatFunc F) * cubicRat W = RatFunc.C (4 : F) * cubicRat W
    congr 1
    simp only [map_ofNat]
  rw [hmapDen]
  rw [natDegree_num_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := duplicationNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    hden hcop]
  exact duplicationNumerator_natDegree W

private lemma d_eq_one_of_point_eq_Q [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_one_of_point_eq_neg_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_four_of_point_eq_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W + Q W) : d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma d_eq_four_of_point_eq_neg_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -(Q W + Q W)) :
    d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma generic_neighbor_degree_identity (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    {hMinus : (twist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (twist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ cubicRat W * RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (twist W).toAffine.Point) + Q W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (twist W).toAffine.Point) - Q W)
    (hdegree : (paperX W x).denom.natDegree <
      (paperX W x).num.natDegree)
    (hdegreeMinus : (paperX W xMinus).denom.natDegree <
      (paperX W xMinus).num.natDegree)
    (hdegreePlus : (paperX W xPlus).denom.natDegree <
      (paperX W xPlus).num.natDegree) :
    (paperX W xMinus).num.natDegree +
        (paperX W xPlus).num.natDegree =
      2 * (paperX W x).num.natDegree + 2 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus = addQX W x y := by
    exact hplusEq.1
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (twist W).toAffine.Point) - Q W =
    -(-(.some x y hxy : (twist W).toAffine.Point) + Q W) by abel] at hminusEq
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
    at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus = subQX W x y := by
    exact hminusEq.1
  have hrPlus :
      paperX W xPlus =
        (additionCommon W (paperX W x) -
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxPlus]
    exact paperX_addX_Q_common W hxy hxQ
  have hrMinus :
      paperX W xMinus =
        (additionCommon W (paperX W x) +
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxMinus]
    exact paperX_neg_addX_Q_common W hxy hxQ
  have heq := paper_coordinates_equation W hxy
  have hdiff := X_sub_paperX_ne_zero W hxQ
  have hprod := symmetricOutput_pair_product W heq hdiff
  have hsum := symmetricOutput_pair_sum W (paperX W x) (paperY W y) hdiff
  rw [← hrPlus, ← hrMinus] at hprod hsum
  have hprod' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 0) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus * paperX W xPlus := by
    simpa only [mul_comm] using hprod
  have hsum' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 1) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus + paperX W xPlus := by
    simpa only [add_comm] using hsum
  have hpoly : X * (paperX W x).denom - (paperX W x).num ≠ 0 :=
    X_mul_denom_sub_num_ne_zero hdiff
  have hprimitive := primitive_symmetricOutput W
    (RatFunc.isCoprime_num_denom (paperX W x)) hpoly
  have hout2 :
      symmetricOutput W (paperX W x).num (paperX W x).denom 2 ≠ 0 := by
    rw [symmetricOutput_two]
    exact pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout2
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod' hsum'
  have hcenter := symmetricOutput_zero_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma d_recurrence [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W (n - 1) + d hchar W (n + 1) = 2 * d hchar W n + 2 := by
  cases hn : point hchar W n with
  | zero =>
      have hplus := point_add_one hchar W n
      have hminus := point_sub_one hchar W n
      rw [hn] at hplus hminus
      have hplusQ : point hchar W (n + 1) = Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : point hchar W (n - 1) = -Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := d_eq_one_of_point_eq_Q hchar W hplusQ
      have hdMinus := d_eq_one_of_point_eq_neg_Q hchar W hminusQ
      have hd : d hchar W n = 0 := by simp [d, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : point hchar W (n - 1) with
      | zero =>
          have hsub := point_sub_one hchar W n
          rw [hn, hminusPoint] at hsub
          have hnQ : point hchar W n = Q W := by
            have hxyQ :
                (.some x y hxy : (twist W).toAffine.Point) = Q W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := point_add_one hchar W n
          rw [hnQ] at hplus
          have hd := d_eq_one_of_point_eq_Q hchar W hnQ
          have hdPlus := d_eq_four_of_point_eq_two_Q hchar W hplus
          have hdMinus : d hchar W (n - 1) = 0 := by
            simp [d, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : point hchar W (n + 1) with
          | zero =>
              have hadd := point_add_one hchar W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : point hchar W n = -Q W := by
                have htranslated := congrArg
                  (fun P : (twist W).toAffine.Point ↦ P - Q W) hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (twist W).toAffine.Point) = -Q W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := point_sub_one hchar W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  point hchar W (n - 1) = -(Q W + Q W) := by
                calc
                  point hchar W (n - 1) = -Q W - Q W := hminus
                  _ = -(Q W + Q W) := by abel
              have hd := d_eq_one_of_point_eq_neg_Q hchar W hnNegQ
              have hdMinus :=
                d_eq_four_of_point_eq_neg_two_Q hchar W hminusNegTwo
              have hdPlus : d hchar W (n + 1) = 0 := by
                simp [d, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := point_add_one hchar W n
              have hminus := point_sub_one hchar W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ Q W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ -Q W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (twist W).toAffine.Nonsingular
                  (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (q_equation W)
              have hxQ : x ≠ cubicRat W * RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
              have hdegree :=
                num_natDegree_gt_denom_natDegree hchar W hn
              have hdegreeMinus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hminusPoint
              have hdegreePlus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hplusPoint
              have hgeneric := generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [d, hn, hminusPoint, hplusPoint, paperX] using hgeneric

/-- Manin's numerator-degree sequence in odd characteristic has the initial values, recurrence,
and zero separation needed for the Hasse bound. -/
theorem manin_degree_data_of_isCharNeTwoNF [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 3
  · exact manin_degree_data_of_card_eq_three hF W
  · exact ⟨{
      d := d (ringChar_ne_two W) W
      zero := d_zero (ringChar_ne_two W) W
      negOne := d_neg_one (ringChar_ne_two W) W hF
      recurrence := d_recurrence (ringChar_ne_two W) W
      noAdjacentZeros := noAdjacentZeros (ringChar_ne_two W) W }⟩
end
