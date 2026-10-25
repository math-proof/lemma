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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
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

lemma superD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W + superQ W) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

lemma superD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -(superQ W + superQ W)) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

lemma superD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∀ n, superD W (n - 1) + superD W (n + 1) = 2 * superD W n + 2 := by
  intro n
  cases hn : superPoint W n with
  | zero =>
      have hplus := superPoint_add_one W n
      have hminus := superPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : superPoint W (n + 1) = superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : superPoint W (n - 1) = -superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := superD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := superD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : superD W n = 0 := by simp [superD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : superPoint W (n - 1) with
      | zero =>
          have hsub := superPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : superPoint W n = superQ W := by
            have hxyQ :
                (.some x y hxy : (superTwist W).toAffine.Point) = superQ W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := superPoint_add_one W n
          rw [hnQ] at hplus
          have hd := superD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := superD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : superD W (n - 1) = 0 := by
            simp [superD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : superPoint W (n + 1) with
          | zero =>
              have hadd := superPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : superPoint W n = -superQ W := by
                have htranslated := congrArg
                  (fun P : (superTwist W).toAffine.Point ↦ P - superQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (superTwist W).toAffine.Point) =
                      -superQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := superPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  superPoint W (n - 1) = -(superQ W + superQ W) := by
                calc
                  superPoint W (n - 1) = -superQ W - superQ W := hminus
                  _ = -(superQ W + superQ W) := by abel
              have hd := superD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                superD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : superD W (n + 1) = 0 := by
                simp [superD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := superPoint_add_one W n
              have hminus := superPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠ superQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠
                    -superQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (superQ_equation W)
              have hxQ : x ≠ RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
              have hdegree := super_num_degree W hxy
              have hdegreeMinus := super_num_degree W hMinus
              have hdegreePlus := super_num_degree W hPlus
              have hgeneric := super_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [superD, hn, hminusPoint, hplusPoint] using hgeneric

lemma supersingular_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := superD W
    zero := superD_zero W
    negOne := superD_neg_one W
    recurrence := superD_recurrence W
    noAdjacentZeros := superNoAdjacentZeros W }⟩

/-- Manin's degree computation in either characteristic-two normal form. -/
theorem manin_degree_data_of_isCharTwoNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 2
  · exact manin_degree_data_of_card_eq_two hF W
  · by_cases hF' : Nat.card F = 4
    · exact manin_degree_data_of_card_eq_four hF' W
    · cases ‹W.IsCharTwoNF› with
      | of_j_ne_zero => exact ordinary_degree_computation W
      | of_j_eq_zero => exact supersingular_degree_computation W

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
