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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part14
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

lemma ordinaryD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W + ordinaryQ W) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

lemma ordinaryD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -(ordinaryQ W + ordinaryQ W)) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

lemma ordinaryD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∀ n, ordinaryD W (n - 1) + ordinaryD W (n + 1) = 2 * ordinaryD W n + 2 := by
  intro n
  cases hn : ordinaryPoint W n with
  | zero =>
      have hplus := ordinaryPoint_add_one W n
      have hminus := ordinaryPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : ordinaryPoint W (n + 1) = ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : ordinaryPoint W (n - 1) = -ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := ordinaryD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := ordinaryD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : ordinaryD W n = 0 := by simp [ordinaryD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : ordinaryPoint W (n - 1) with
      | zero =>
          have hsub := ordinaryPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : ordinaryPoint W n = ordinaryQ W := by
            have hxyQ :
                (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                  ordinaryQ W := sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := ordinaryPoint_add_one W n
          rw [hnQ] at hplus
          have hd := ordinaryD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := ordinaryD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : ordinaryD W (n - 1) = 0 := by
            simp [ordinaryD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : ordinaryPoint W (n + 1) with
          | zero =>
              have hadd := ordinaryPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : ordinaryPoint W n = -ordinaryQ W := by
                have htranslated := congrArg
                  (fun P : (ordinaryTwist W).toAffine.Point ↦ P - ordinaryQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                      -ordinaryQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := ordinaryPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  ordinaryPoint W (n - 1) =
                    -(ordinaryQ W + ordinaryQ W) := by
                calc
                  ordinaryPoint W (n - 1) = -ordinaryQ W - ordinaryQ W :=
                    hminus
                  _ = -(ordinaryQ W + ordinaryQ W) := by abel
              have hd := ordinaryD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                ordinaryD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : ordinaryD W (n + 1) = 0 := by
                simp [ordinaryD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := ordinaryPoint_add_one W n
              have hminus := ordinaryPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    ordinaryQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    -ordinaryQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (ordinaryTwist W).toAffine.Nonsingular
                  (RatFunc.X ^ 3) 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (ordinaryQ_equation W)
              have hxQ : x ≠ RatFunc.X ^ 3 := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
              have hdegree := ordinary_num_degree W hn
              have hdegreeMinus := ordinary_num_degree W hminusPoint
              have hdegreePlus := ordinary_num_degree W hplusPoint
              have hgeneric := ordinary_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [ordinaryD, hn, hminusPoint, hplusPoint] using hgeneric

lemma ordinary_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := ordinaryD W
    zero := ordinaryD_zero W
    negOne := ordinaryD_neg_one W
    recurrence := ordinaryD_recurrence W
    noAdjacentZeros := ordinaryNoAdjacentZeros W }⟩

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
