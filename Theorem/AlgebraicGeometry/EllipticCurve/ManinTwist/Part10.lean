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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part10
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

lemma card_gt_three [Finite F] (hchar : ringChar F ≠ 2)
    (hcard : Nat.card F ≠ 3) : 3 < Nat.card F := by
  obtain ⟨k, hk⟩ := card_odd hchar
  have hlarge := Finite.one_lt_card (α := F)
  omega

lemma twice_half_card_sub_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

lemma twice_half_card_add_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 1) / 2) = Nat.card F + 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

lemma minusOneNumerator_eq [Finite F] (hchar : ringChar F ≠ 2)
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

lemma minusOneNumerator_natDegree [Finite F]
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

lemma pZeroX_ne_qX [Finite F] (W : WeierstrassCurve F) :
    pZeroX W ≠ cubicRat W * RatFunc.X := by
  intro h
  have hpow : RatFunc.X ^ Nat.card F = RatFunc.X :=
    mul_left_cancel₀ (cubicRat_ne_zero W) h
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at hdegree
  simp only [mul_one] at hdegree
  have hcard := Finite.one_lt_card (α := F)
  omega

lemma paperY_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W (pZeroY W) = cubicRat W ^ ((Nat.card F - 1) / 2) := by
  have hexponent :
      (Nat.card F + 3) / 2 = (Nat.card F - 1) / 2 + 2 := by
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  unfold paperY pZeroY
  rw [hexponent, pow_add]
  field_simp [cubicRat_ne_zero W]

lemma cubic_mul_eulerPolynomial [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    cubic W * eulerPolynomial W = cubic W ^ ((Nat.card F + 1) / 2) := by
  unfold eulerPolynomial
  rw [show cubic W * cubic W ^ ((Nat.card F - 1) / 2) =
    cubic W ^ ((Nat.card F - 1) / 2 + 1) by
      exact (pow_succ' _ _).symm]
  congr 1
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

lemma minusOneNumerator_canceled_eq [Finite F]
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

lemma paperY_neg_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) =
      -(cubicRat W ^ ((Nat.card F - 1) / 2)) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  rw [show paperY W (-pZeroY W) = -paperY W (pZeroY W) by
    unfold paperY
    exact neg_div _ _]
  rw [paperY_pZeroY hchar W]

lemma algebraMap_minusOneNumerator [Finite F]
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

lemma paperX_negPZero_add_Q [Finite F]
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

lemma point_neg_one_eq_some [Finite F]
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

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
