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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
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

lemma X_sub_paperX_ne_zero (W : WeierstrassCurve F)
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

lemma Q_y_ne_negY [Finite F] (hchar : ringChar F ≠ 2)
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

lemma paperX_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
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

lemma num_natDegree_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
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

lemma d_eq_one_of_point_eq_Q [Finite F] (hchar : ringChar F ≠ 2)
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

lemma d_eq_one_of_point_eq_neg_Q [Finite F]
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

lemma d_eq_four_of_point_eq_two_Q [Finite F]
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

lemma d_eq_four_of_point_eq_neg_two_Q [Finite F]
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

lemma generic_neighbor_degree_identity (W : WeierstrassCurve F)
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

lemma d_recurrence [Finite F] (hchar : ringChar F ≠ 2)
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
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
