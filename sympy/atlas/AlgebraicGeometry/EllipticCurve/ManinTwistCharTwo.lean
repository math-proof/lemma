/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import sympy.atlas.AlgebraicGeometry.EllipticCurve.PointCount
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

private def quadraticDegree (q : ℕ) (a n : ℤ) : ℤ :=
  n ^ 2 + a * n + q

private def nonnegativeQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ quadraticDegree q a n)
    (hnoAdjacent : ∀ n, quadraticDegree q a n = 0 →
      quadraticDegree q a (n + 1) = 0 → False) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic q N a ha
    (by simpa only [quadraticDegree] using hnonneg)
    (by simpa only [quadraticDegree] using hnoAdjacent)

private def positiveQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ)) (hpos : ∀ n, 0 < quadraticDegree q a n) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  nonnegativeQuadraticDegreeData q N a ha (fun n ↦ (hpos n).le)
    (fun n hn _ ↦ by nlinarith [hpos n])

private def frobeniusTail (h k : F[X]) : ℕ → F[X]
  | 0 => 0
  | e + 1 => frobeniusTail h k e ^ 2 + k ^ (2 ^ (e + 1) - 2) * h

private lemma frobeniusTail_identity [CharP F 2] (h k : F[X]) (e : ℕ) :
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

private def charTwoExponent [Finite F] : ℕ := Nat.log 2 (Nat.card F)

private lemma card_eq_two_pow [Finite F] [CharP F 2] :
    Nat.card F = 2 ^ charTwoExponent (F := F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  obtain ⟨e, _, he⟩ := @FiniteField.card F _ fintypeF 2 _
  unfold charTwoExponent
  rw [@Nat.card_eq_fintype_card F fintypeF, he, Nat.log_pow (by norm_num)]

private def charTwoFiber (b c : F) :=
  {y : F // y ^ 2 + b * y = c}

private instance charTwoFiberFinite [Finite F] (b c : F) :
    Finite (charTwoFiber b c) := by
  unfold charTwoFiber
  infer_instance

private def frobeniusValue (c b : F) : ℕ → F
  | 0 => 0
  | e + 1 => frobeniusValue c b e ^ 2 + b ^ (2 ^ (e + 1) - 2) * c

private lemma frobeniusValue_eq_zero_of_mem_fiber [Finite F] [CharP F 2]
    {b c y : F} (hb : b ≠ 0) (hy : y ^ 2 + b * y = c) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hyq : y ^ Nat.card F = y := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card y
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have h := frobenius_pow_eq_linear_add_value hy
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hyq, hbq1, one_mul] at h
  have hzero : (0 : F) = frobeniusValue c b (charTwoExponent (F := F)) :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hzero.symm

private lemma frobeniusValue_eq_zero_or_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 ∨
      frobeniusValue c b (charTwoExponent (F := F)) = b := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq : b ^ Nat.card F = b := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card b
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hcq : c ^ Nat.card F = c := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card c
  have htail := congrArg (Polynomial.eval (0 : F))
    (frobeniusTail_identity (C c) (C b) (charTwoExponent (F := F)))
  simp only [eval_add, eval_mul, eval_pow, eval_C] at htail
  rw [eval_frobeniusTail, eval_C, eval_C,
    ← card_eq_two_pow (F := F), hbq, hcq] at htail
  rw [show b ^ (2 * (Nat.card F - 1)) = 1 by
    rw [mul_comm, pow_mul, hbq1, one_pow], one_mul] at htail
  rw [CharTwo.add_self_eq_zero] at htail
  have hfactor :
      frobeniusValue c b (charTwoExponent (F := F)) *
        (frobeniusValue c b (charTwoExponent (F := F)) + b) = 0 := by
    calc
      _ = frobeniusValue c b (charTwoExponent (F := F)) ^ 2 +
          b * frobeniusValue c b (charTwoExponent (F := F)) := by ring
      _ = 0 := htail
  rcases mul_eq_zero.mp hfactor with hzero | heq
  · exact Or.inl hzero
  · exact Or.inr (by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left heq)

private def charTwoQuadratic (b c : F) : F[X] :=
  X ^ 2 + C b * X + C c

private def frobeniusQuotient (b c : F) : ℕ → F[X]
  | 0 => 0
  | e + 1 =>
      charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
        C (b ^ (2 ^ (e + 1) - 2))

private def charTwoFrobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private lemma exists_mem_charTwoFiber_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    ∃ y, y ^ 2 + b * y = c := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hmod := frobenius_polynomial_mod_quadratic b c
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hbq1, hvalue] at hmod
  simp only [map_one, one_mul, map_zero, add_zero] at hmod
  have hmod' :
      charTwoFrobeniusPolynomial =
        charTwoQuadratic b c *
          frobeniusQuotient b c (charTwoExponent (F := F)) := by
    unfold charTwoFrobeniusPolynomial
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hmod
  have hdiv : charTwoQuadratic b c ∣
      (charTwoFrobeniusPolynomial : F[X]) :=
    ⟨frobeniusQuotient b c (charTwoExponent (F := F)), hmod'⟩
  have hsplit : (charTwoQuadratic b c).Splits :=
    charTwoFrobeniusPolynomial_splits.of_dvd
      charTwoFrobeniusPolynomial_ne_zero hdiv
  have hnatDegree : (charTwoQuadratic b c).natDegree = 2 := by
    exact (Polynomial.isMonicOfDegree_add_add_two b c).natDegree_eq
  have hdegree : (charTwoQuadratic b c).degree ≠ 0 := by
    apply Polynomial.degree_ne_of_natDegree_ne
    rw [hnatDegree]
    norm_num
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdegree
  refine ⟨y, ?_⟩
  unfold charTwoQuadratic at hy
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
  have hy' : y ^ 2 + b * y = -c := eq_neg_of_add_eq_zero_left hy
  simpa only [CharTwo.neg_eq] using hy'

private lemma charTwoFiber_card_eq_two_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    Nat.card (charTwoFiber b c) = 2 := by
  obtain ⟨y, hy⟩ := exists_mem_charTwoFiber_of_value_eq_zero hb hvalue
  exact charTwoFiber_card_eq_two hb hy

private lemma charTwoFiber_card_eq_zero_of_value_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = b) :
    Nat.card (charTwoFiber b c) = 0 := by
  apply charTwoFiber_card_eq_zero
  rintro ⟨y, hy⟩
  have hzero := frobeniusValue_eq_zero_of_mem_fiber hb hy
  exact hb (hvalue ▸ hzero)

private def ordinaryH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₆

private def ordinaryU [Finite F] (W : WeierstrassCurve F) : F[X] :=
  X * frobeniusTail (ordinaryH W) X (charTwoExponent (F := F))

private lemma ordinaryH_pow_card [Finite F] (W : WeierstrassCurve F) :
    ordinaryH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [ordinaryH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma ordinaryU_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryU W ^ 2 + X ^ (Nat.card F + 1) * ordinaryU W =
      X ^ 2 * ordinaryH W ^ Nat.card F + X ^ (2 * Nat.card F) * ordinaryH W := by
  have htail := frobeniusTail_identity (ordinaryH W) X
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  have hterm :
      X ^ 2 * (X ^ (2 * (Nat.card F - 1)) * ordinaryH W) =
        X ^ (2 * Nat.card F) * ordinaryH W := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  unfold ordinaryU
  calc
    (X * frobeniusTail (ordinaryH W) X charTwoExponent) ^ 2 +
        X ^ (Nat.card F + 1) *
          (X * frobeniusTail (ordinaryH W) X charTwoExponent) =
      X ^ 2 * (frobeniusTail (ordinaryH W) X charTwoExponent ^ 2 +
        X ^ Nat.card F * frobeniusTail (ordinaryH W) X charTwoExponent) := by
          ring
    _ = X ^ 2 * (ordinaryH W ^ Nat.card F +
        X ^ (2 * (Nat.card F - 1)) * ordinaryH W) := by rw [htail]
    _ = _ := by rw [mul_add, hterm]

private def ordinaryTwist (W : WeierstrassCurve F) :
    WeierstrassCurve (RatFunc F) :=
  ⟨RatFunc.X, RatFunc.X ^ 3 + RatFunc.C W.a₆, 0, 0,
    RatFunc.C W.a₆ * RatFunc.X ^ 6⟩

private lemma ordinaryTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).Δ = RatFunc.C W.a₆ * RatFunc.X ^ 12 := by
  simp only [ordinaryTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, zero_add, sub_zero, CharTwo.neg_eq]
  ring_nf

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, ordinaryTwist_discriminant,
    isUnit_iff_ne_zero]
  apply mul_ne_zero
  · have hb : W.a₆ ≠ 0 := by
      have h := W.Δ'.ne_zero
      rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
      exact h
    intro hC
    apply hb
    apply RatFunc.C_injective
    simpa using hC
  · exact pow_ne_zero 12 RatFunc.X_ne_zero

private lemma ordinaryQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (RatFunc.X ^ 3) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ordinaryTwist]
  ring_nf
  rw [CharTwo.two_eq_zero]
  simp

private def ordinaryQ [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryQ_equation W)

private def ordinaryPZeroX [Finite F] : RatFunc F :=
  RatFunc.X ^ (Nat.card F + 2)

private def ordinaryPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (X ^ 2 * ordinaryU W)

private lemma ordinary_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (X ^ 2 * ordinaryU W) ^ 2 +
        X * X ^ (Nat.card F + 2) * (X ^ 2 * ordinaryU W) =
      (X ^ (Nat.card F + 2)) ^ 3 +
        (X ^ 3 + C W.a₆) * (X ^ (Nat.card F + 2)) ^ 2 +
        C W.a₆ * X ^ 6 := by
  have hu := ordinaryU_identity W
  have hh := ordinaryH_pow_card W
  rw [hh] at hu
  unfold ordinaryH at hu
  have hcancel :
      C W.a₂ * X ^ (2 * Nat.card F + 6) +
        C W.a₂ * X ^ (2 * Nat.card F + 6) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination X ^ 4 * hu + hcancel

private lemma ordinaryPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (ordinaryPZeroX (F := F))
      (ordinaryPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (ordinary_pZero_polynomial_equation W)
  simpa only [ordinaryTwist, ordinaryPZeroX, ordinaryPZeroY, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def ordinaryPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryPZero_equation W)

private local instance : DecidableEq F := Classical.decEq F

private def ordinaryPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    (ordinaryTwist W).toAffine.Point := ordinaryPZero W + n • ordinaryQ W

private def ordinaryPaperX (x : RatFunc F) : RatFunc F := x / RatFunc.X ^ 2

private def ordinaryPaperY (y : RatFunc F) : RatFunc F := y / RatFunc.X ^ 3

private def ordinaryBadAtInfinity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (ordinaryPaperX x).intDegree ≤ 0

private def ordinaryD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) : ℕ :=
  match ordinaryPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (ordinaryPaperX x)).natDegree

private def ordinaryMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W

private lemma ordinaryU_derivative [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).derivative =
      frobeniusTail (ordinaryH W) X (charTwoExponent (F := F)) +
        X ^ (Nat.card F + 1) := by
  have hexponent : 0 < charTwoExponent (F := F) := by
    have hcard : 1 < Nat.card F := Finite.one_lt_card
    rw [card_eq_two_pow (F := F)] at hcard
    exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  unfold ordinaryU
  rw [derivative_mul, derivative_X,
    derivative_frobeniusTail_ordinary W _ hexponent]
  rw [← card_eq_two_pow (F := F)]
  simp only [one_mul]
  rw [mul_comm, ← pow_succ]

private lemma charTwoExponent_pos [Finite F] [CharP F 2] :
    0 < charTwoExponent (F := F) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  rw [card_eq_two_pow (F := F)] at hcard
  exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard

private lemma ordinaryU_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).natDegree =
      1 + 3 * 2 ^ (charTwoExponent (F := F) - 1) := by
  unfold ordinaryU
  have htailDegree := frobeniusTail_ordinary_natDegree W
    (charTwoExponent (F := F)) (charTwoExponent_pos (F := F))
  have htail : frobeniusTail (ordinaryH W) X
      (charTwoExponent (F := F)) ≠ 0 := by
    intro hzero
    rw [hzero] at htailDegree
    simp at htailDegree
  rw [natDegree_mul X_ne_zero htail, natDegree_X, htailDegree]

private lemma ordinaryMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk]
    rw [pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hU : (ordinaryU W).natDegree ≤ 2 * Nat.card F := by
    rw [ordinaryU_natDegree W]
    change 1 + 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have hfirst : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    have hsecond : (X ^ (Nat.card F + 1) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hfirst hsecond)) hU)
  have heq : ordinaryMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold ordinaryMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma eval_derivative_ordinaryMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).derivative.eval x =
      x + frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hcoeff3 : (((Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  have hexponent3 : Nat.card F + 1 - 1 = Nat.card F := by omega
  unfold ordinaryMinusOneNumerator
  simp only [derivative_add, derivative_pow, derivative_X,
    ordinaryU_derivative, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_one, eval_frobeniusTail, hcoeff1, hcoeff2, hcoeff3, one_mul,
    zero_mul, hexponent1, hexponent3, hx2q, hxq, hxq1]
  have hcancel : x ^ 2 + x ^ 2 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

private lemma ordinaryTailValue_zero_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    frobeniusValue ((ordinaryH W).eval 0) 0
      (charTwoExponent (F := F)) ≠ 0 := by
  rw [frobeniusValue_zero_coefficient _ _ (charTwoExponent_pos (F := F))]
  simp only [ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_add]
  exact pow_ne_zero _ (ordinary_a₆_ne_zero W)

private lemma ordinaryEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + x * y = (ordinaryH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₃_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₄_of_isCharTwoJNeZeroNF, one_mul, zero_mul,
    add_zero, ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivOrdinaryFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber x ((ordinaryH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (ordinaryEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (ordinaryEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma ordinaryMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : ordinaryMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := ordinaryMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma rootMultiplicity_ordinaryNumerator_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) = 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot 0 := by
    change (ordinaryMinusOneNumerator W).eval 0 = 0
    rw [eval_ordinaryMinusOneNumerator]
    simp
  have hpositive : 0 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
    (Polynomial.rootMultiplicity_pos hN).mpr hroot
  have hnotTwo : ¬1 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) := by
    intro htwo
    have hderivativeRoot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mp htwo |>.2
    have hderivative := eval_derivative_ordinaryMinusOneNumerator W 0
    rw [show (ordinaryMinusOneNumerator W).derivative.eval 0 = 0 from
      hderivativeRoot] at hderivative
    simp only [zero_add] at hderivative
    exact ordinaryTailValue_zero_ne_zero W hderivative.symm
  omega

private lemma ordinaryNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = x) :
    (X - C x) ^ 2 ∣ ordinaryMinusOneNumerator W := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot x := by
    change (ordinaryMinusOneNumerator W).eval x = 0
    rw [eval_ordinaryMinusOneNumerator, hvalue]
    simpa only [pow_two] using CharTwo.add_self_eq_zero (x * x)
  have hderivativeRoot : (ordinaryMinusOneNumerator W).derivative.IsRoot x := by
    change (ordinaryMinusOneNumerator W).derivative.eval x = 0
    rw [eval_derivative_ordinaryMinusOneNumerator, hvalue]
    exact CharTwo.add_self_eq_zero x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private def ordinaryMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (ordinaryMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_ordinaryMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (x : F) :
    Multiset.count x (ordinaryMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hx : x = 0
  · subst x
    have hlinearN : X - C 0 ∣ ordinaryMinusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (ordinaryMinusOneNumerator W).eval 0 = 0
      rw [eval_ordinaryMinusOneNumerator]
      simp
    have hlinearL' : X - C 0 ∣
        (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
      hlinearL.trans ⟨charTwoFrobeniusPolynomial, by ring⟩
    have hcommon : X - C 0 ∣ ordinaryMinusOneGCD W := by
      unfold ordinaryMinusOneGCD
      exact dvd_gcd hlinearN hlinearL'
    have hlower : 1 ≤
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper :
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤
            Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN 0
        _ = 1 := rootMultiplicity_ordinaryNumerator_zero W
    have hroot : Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot, charTwoFiber_card_eq_one]
  · rcases frobeniusValue_eq_zero_or_eq
        (c := (ordinaryH W).eval x) hx with hvalue | hvalue
    · have hupper :
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
          _ = 0 := rootMultiplicity_ordinaryNumerator_eq_zero W x hx hvalue
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_two_of_value_eq_zero hx hvalue]
    · have hcommon : (X - C x) ^ 2 ∣ ordinaryMinusOneGCD W := by
        unfold ordinaryMinusOneGCD
        exact dvd_gcd (ordinaryNumerator_sq_dvd_of_value_eq W x hvalue)
          hlinearLsq
      have hlower : 2 ≤
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL : Polynomial.rootMultiplicity x
          ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_charTwoFrobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 2 :=
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x
                ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_zero_of_value_eq hx hvalue]

private lemma ordinaryMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (ordinaryMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots) =
        (ordinaryMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (ordinaryMinusOneGCD W).roots) (by simp))
  calc
    (ordinaryMinusOneGCD W).natDegree =
        (ordinaryMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_ordinaryMinusOneGCD W x

private lemma ordinaryMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x)) =
      2 * Nat.card F := by
  rw [ordinaryMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) +
        Nat.card (charTwoFiber x ((ordinaryH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two x _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma ordinaryMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : ordinaryMinusOneGCD W *
      (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W) =
        ordinaryMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, ordinaryMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := ordinaryMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_ordinaryMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact ordinaryMinusOneQuotient_natDegree W

private lemma ordinaryPaperX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [ordinaryPaperX_addX_Q_eq W ordinaryPZeroX_ne_QX]
  rw [ordinaryPaperX_pZeroX, ordinaryPaperY_neg_pZeroY W]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [ordinaryMinusOneNumerator, map_add, map_pow,
    RatFunc.algebraMap_X, sub_eq_add_neg, CharTwo.neg_eq]
  let q := Nat.card F
  let t : RatFunc F := RatFunc.X
  let r := t ^ q
  let u := algebraMap F[X] (RatFunc F) (ordinaryU W)
  let a := RatFunc.C W.a₂
  let b := RatFunc.C W.a₆
  let s := u / t + r
  let L := r + t
  let n := t ^ (2 * q + 1) + t ^ (q + 2) + t ^ (q + 1) + u
  change (s / L) ^ 2 + s / L + b / t ^ 2 + r = n / L ^ 2
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have hL : L ≠ 0 := by
    dsimp only [L, r, t, q]
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hu := congrArg (algebraMap F[X] (RatFunc F)) (ordinaryU_identity W)
  rw [ordinaryH_pow_card W] at hu
  simp only [ordinaryH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hu
  change u ^ 2 + t ^ (q + 1) * u =
    t ^ 2 * (t ^ (3 * q) + a * t ^ (2 * q) + b) +
      t ^ (2 * q) * (t ^ 3 + a * t ^ 2 + b) at hu
  have htq1 : t ^ (q + 1) = t * r := by
    dsimp only [r]
    rw [pow_succ]
    ring
  have ht2q : t ^ (2 * q) = r ^ 2 := by
    dsimp only [r]
    calc
      t ^ (2 * q) = t ^ (q * 2) := by congr 1; omega
      _ = (t ^ q) ^ 2 := pow_mul t q 2
  have ht3q : t ^ (3 * q) = r ^ 3 := by
    dsimp only [r]
    calc
      t ^ (3 * q) = t ^ (q * 3) := by congr 1; omega
      _ = (t ^ q) ^ 3 := pow_mul t q 3
  rw [htq1, ht2q, ht3q] at hu
  have hu' : u ^ 2 + t * r * u =
      t ^ 2 * r ^ 3 + b * t ^ 2 + t ^ 3 * r ^ 2 + b * r ^ 2 := by
    have hcancel : a * t ^ 2 * r ^ 2 + a * t ^ 2 * r ^ 2 = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination hu + hcancel
  dsimp only [s, n]
  field_simp [ht, hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hu' +
    (u * t * t ^ q + t * t ^ q * b + t ^ 2 * t ^ (q * 2) +
      t ^ 2 * t ^ (q * 3) + t ^ 2 * b + t ^ 3 * t ^ (q * 2) +
        t ^ (q * 2) * b) * htwo

private lemma ordinaryPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∃ y hxy, ordinaryPoint W (-1) =
      .some
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) y hxy := by
  have hp : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryPZero_equation W)
  have hneg : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F))
      ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
        (ordinaryPZeroY W)) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -ordinaryPZero W = .some (ordinaryPZeroX (F := F))
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) hneg := by
    rw [show ordinaryPZero W =
      .some (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) ordinaryPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryQ_equation W))
  rw [← hnegP, ← show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
    at hadd
  have hpoint : ordinaryPoint W (-1) =
      -(-ordinaryPZero W + ordinaryQ W) := by
    unfold ordinaryPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma ordinaryD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := ordinaryPoint_neg_one_eq_some W
  unfold ordinaryD
  rw [hpoint]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)))).natDegree = _
  rw [ordinaryPaperX_negPZero_add_Q W]
  rw [num_natDegree_ordinaryMinusOneRat W]
  exact (ordinaryPointCount_eq_fiber_sum W).symm

private def ordinaryNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + C W.a₆ * g ^ 2

private def ordinaryNeighborSecond (f g : F[X]) : F[X] :=
  X * f * g

private def neighborDenominator (f g : F[X]) : F[X] :=
  (X * g + f) ^ 2

private lemma ordinary_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    {hMinus : (ordinaryTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (ordinaryTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W)
    (hdegree : (ordinaryPaperX x).denom.natDegree <
      (ordinaryPaperX x).num.natDegree)
    (hdegreeMinus : (ordinaryPaperX xMinus).denom.natDegree <
      (ordinaryPaperX xMinus).num.natDegree)
    (hdegreePlus : (ordinaryPaperX xPlus).denom.natDegree <
      (ordinaryPaperX xPlus).num.natDegree) :
    (ordinaryPaperX xMinus).num.natDegree +
        (ordinaryPaperX xPlus).num.natDegree =
      2 * (ordinaryPaperX x).num.natDegree + 2 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0) :=
    hplusEq.1
  have hneg : (ordinaryTwist W).toAffine.Nonsingular x
      ((ordinaryTwist W).toAffine.negY x y) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W =
    -(-(.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W) by
      abel] at hminusEq
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : ordinaryPaperX xPlus =
      (ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxPlus]
    exact ordinaryPaperX_addX_Q_eq W hxQ
  have hrMinus : ordinaryPaperX xMinus =
      ((ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        (ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X) +
            RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxMinus, ordinaryPaperX_addX_Q_eq W hxQ,
      ordinaryPaperY_negY W]
  have heq := ordinary_paper_coordinates_equation W hxy
  have hdiff : RatFunc.X + ordinaryPaperX x ≠ 0 := by
    intro hzero
    apply hxQ
    have hr : ordinaryPaperX x = RatFunc.X := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
    unfold ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hpairProd := ordinary_neighbor_pair_product W heq hdiff
  have hpairSum := ordinary_neighbor_pair_sum W
    (s := ordinaryPaperY y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborFirst W (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus * ordinaryPaperX xPlus := by
    rw [ordinaryNeighborFirst_ratio]
    calc
      _ = ordinaryPaperX xPlus * ordinaryPaperX xMinus := hpairProd.symm
      _ = ordinaryPaperX xMinus * ordinaryPaperX xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborSecond (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus + ordinaryPaperX xPlus := by
    rw [ordinaryNeighborSecond_ratio]
    calc
      _ = ordinaryPaperX xPlus + ordinaryPaperX xMinus := hpairSum.symm
      _ = ordinaryPaperX xMinus + ordinaryPaperX xPlus := by ring
  have hpoly : X * (ordinaryPaperX x).denom + (ordinaryPaperX x).num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := ordinaryNeighbor_primitive W
    (RatFunc.isCoprime_num_denom (ordinaryPaperX x)) hpoly
  have hout : neighborDenominator (ordinaryPaperX x).num
      (ordinaryPaperX x).denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := ordinaryNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma ordinaryD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma ordinaryD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private def ordinaryDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C W.a₆

private lemma ordinaryD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
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

private lemma ordinaryD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
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

private lemma ordinaryD_recurrence [Finite F] [CharP F 2]
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

private lemma ordinary_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := ordinaryD W
    zero := ordinaryD_zero W
    negOne := ordinaryD_neg_one W
    recurrence := ordinaryD_recurrence W
    noAdjacentZeros := ordinaryNoAdjacentZeros W }⟩

private def superH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₄ * X + C W.a₆

private def superV [Finite F] (W : WeierstrassCurve F) : F[X] :=
  frobeniusTail (superH W) (C W.a₃) (charTwoExponent (F := F))

private lemma superH_pow_card [Finite F] (W : WeierstrassCurve F) :
    superH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [superH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma superV_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      superH W ^ Nat.card F + superH W := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  let fintypeF : Fintype F := Fintype.ofFinite F
  have haq : W.a₃ ^ Nat.card F = W.a₃ := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card F _ fintypeF W.a₃
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card_sub_one_eq_one F _ fintypeF W.a₃ ha
  have htail := frobeniusTail_identity (superH W) (C W.a₃)
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hCq : C W.a₃ ^ Nat.card F = C W.a₃ := by rw [← map_pow, haq]
  have hCq1 : C W.a₃ ^ (2 * (Nat.card F - 1)) = 1 := by
    rw [show 2 * (Nat.card F - 1) = (Nat.card F - 1) * 2 by omega,
      pow_mul, ← map_pow, haq1, map_one, one_pow]
  rw [hCq, hCq1, one_mul] at htail
  exact htail

private def superTwist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, 0, RatFunc.C W.a₃, RatFunc.C W.a₄,
    RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X⟩

private lemma superTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) : (superTwist W).Δ = RatFunc.C W.a₃ ^ 4 := by
  simp only [superTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, sub_zero, CharTwo.neg_eq]
  ring_nf
  rw [CharTwo.neg_eq]

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] : (superTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, superTwist_discriminant,
    isUnit_iff_ne_zero]
  apply pow_ne_zero
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  intro hC
  apply ha
  apply RatFunc.C_injective
  simpa using hC

private lemma superQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (superTwist W).toAffine.Equation RatFunc.X 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [superTwist]

private def superQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superQ_equation W)

private def superPZeroX [Finite F] : RatFunc F := RatFunc.X ^ Nat.card F

private def superPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (superV W)

private lemma super_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      (X ^ Nat.card F) ^ 3 + C W.a₄ * X ^ Nat.card F +
        (X ^ 3 + C W.a₄ * X) := by
  rw [superV_identity W, superH_pow_card W]
  unfold superH
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination C W.a₆ * htwo

private lemma superPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Equation (superPZeroX (F := F))
      (superPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (super_pZero_polynomial_equation W)
  simpa only [superTwist, superPZeroX, superPZeroY, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def superPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superPZero_equation W)

private def superPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    (superTwist W).toAffine.Point := superPZero W + n • superQ W

private def superD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (n : ℤ) : ℕ :=
  match superPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num x).natDegree

private def superMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)

private lemma superV_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superV W).natDegree = 3 * 2 ^ (charTwoExponent (F := F) - 1) :=
  frobeniusTail_super_natDegree W _ (charTwoExponent_pos (F := F))

private lemma superMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk, pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hV : (superV W).natDegree ≤ 2 * Nat.card F := by
    rw [superV_natDegree W]
    change 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h₁ : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by rw [natDegree_X_pow]; omega
    have h₂ : (C W.a₄ * (X ^ Nat.card F + X)).natDegree ≤
        2 * Nat.card F := by
      calc
        _ ≤ (X ^ Nat.card F + X : F[X]).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ ≤ max (Nat.card F) 1 := by
          exact (natDegree_add_le _ _).trans (max_le
            (by rw [natDegree_X_pow]; exact le_max_left _ _)
            (by rw [natDegree_X]; exact le_max_right _ _))
        _ ≤ 2 * Nat.card F := by omega
    have h₃ : (C W.a₃ * superV W).natDegree ≤ 2 * Nat.card F :=
      (Polynomial.natDegree_C_mul_le _ _).trans hV
    have h₄ : (C (W.a₃ ^ 2) : F[X]).natDegree ≤ 2 * Nat.card F := by
      rw [natDegree_C]
      omega
    dsimp only [remainder]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le h₁ h₂)) h₃)) h₄)
  have heq : superMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold superMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma superEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔
      y ^ 2 + W.a₃ * y = (superH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJEqZeroNF,
    WeierstrassCurve.a₂_of_isCharTwoJEqZeroNF, zero_mul, add_zero,
    superH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivSuperFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber W.a₃ ((superH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (superEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (superEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma superX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0) =
      algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne superPZeroX_ne_QX]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superPZeroX, superPZeroY, zero_mul, add_zero,
    sub_eq_add_neg, CharTwo.neg_eq]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [superMinusOneNumerator, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hL : (RatFunc.X ^ Nat.card F + RatFunc.X : RatFunc F) ≠ 0 := by
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hv := congrArg (algebraMap F[X] (RatFunc F)) (superV_identity W)
  rw [superH_pow_card W] at hv
  simp only [superH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hv
  field_simp [hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hv +
    ((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃ +
      RatFunc.X ^ (Nat.card F * 3) + RatFunc.C W.a₄ *
        RatFunc.X ^ Nat.card F + RatFunc.C W.a₆ + RatFunc.X ^ 3 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * htwo +
    (-((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃) +
      RatFunc.X * RatFunc.X ^ (Nat.card F * 2) -
      RatFunc.X * RatFunc.C W.a₄ +
      RatFunc.X ^ 2 * RatFunc.X ^ Nat.card F -
      RatFunc.X ^ Nat.card F * RatFunc.C W.a₄ - RatFunc.C W.a₆) * htwo

private lemma superPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∃ y hxy, superPoint W (-1) =
      .some
        ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
            ((superTwist W).toAffine.negY (superPZeroX (F := F))
              (superPZeroY W)) 0)) y hxy := by
  have hp : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F)) (superPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superPZero_equation W)
  have hneg : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F))
      ((superTwist W).toAffine.negY (superPZeroX (F := F))
        (superPZeroY W)) :=
    ((superTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -superPZero W = .some (superPZeroX (F := F))
        ((superTwist W).toAffine.negY (superPZeroX (F := F))
          (superPZeroY W)) hneg := by
    rw [show superPZero W =
      .some (superPZeroX (F := F)) (superPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) superPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superQ_equation W))
  rw [← hnegP, ← show superQ W = .some RatFunc.X 0 _ from rfl] at hadd
  have hpoint : superPoint W (-1) = -(-superPZero W + superQ W) := by
    unfold superPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma eval_derivative_superMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F) :
    (superMinusOneNumerator W).derivative.eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one W.a₃ ha
  have hcard : 2 ≤ Nat.card F := Finite.one_lt_card
  have hamul : W.a₃ * W.a₃ ^ (Nat.card F - 2) = 1 := by
    calc
      W.a₃ * W.a₃ ^ (Nat.card F - 2) =
          W.a₃ ^ (Nat.card F - 2 + 1) := (pow_succ' _ _).symm
      _ = W.a₃ ^ (Nat.card F - 1) := by congr 1; omega
      _ = 1 := haq1
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  unfold superMinusOneNumerator superV
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [derivative_frobeniusTail_super W _ (charTwoExponent_pos (F := F))]
  rw [← card_eq_two_pow (F := F)]
  simp only [derivative_pow, derivative_X, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_one, hcoeff1, hcoeff2, one_mul, zero_mul,
    hexponent1, hx2q, hqcast, add_zero]
  rw [← mul_assoc, hamul, one_mul]
  simp only [mul_one, zero_add]
  exact CharTwo.add_self_eq_zero (x ^ 2 + W.a₄)

private lemma superMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : superMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := superMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma superNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = W.a₃) :
    (X - C x) ^ 2 ∣ superMinusOneNumerator W := by
  have hN := superMinusOneNumerator_ne_zero W
  have hroot : (superMinusOneNumerator W).IsRoot x := by
    change (superMinusOneNumerator W).eval x = 0
    rw [eval_superMinusOneNumerator, hvalue]
    simpa only [pow_two] using
      CharTwo.add_self_eq_zero (W.a₃ * W.a₃)
  have hderivativeRoot : (superMinusOneNumerator W).derivative.IsRoot x := by
    exact eval_derivative_superMinusOneNumerator W x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private def superMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (superMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_superMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F) :
    Multiset.count x (superMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) := by
  have hN := superMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  rcases frobeniusValue_eq_zero_or_eq
      (c := (superH W).eval x) ha with hvalue | hvalue
  · have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 0 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
        _ = 0 := rootMultiplicity_superNumerator_eq_zero W x hvalue
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 0 :=
      Nat.eq_zero_of_le_zero hupper
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_two_of_value_eq_zero ha hvalue]
  · have hcommon : (X - C x) ^ 2 ∣ superMinusOneGCD W := by
      unfold superMinusOneGCD
      exact dvd_gcd (superNumerator_sq_dvd_of_value_eq W x hvalue)
        hlinearLsq
    have hlower : 2 ≤ Polynomial.rootMultiplicity x (superMinusOneGCD W) :=
      (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
    have hrootL : Polynomial.rootMultiplicity x
        ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
      rw [← Polynomial.count_roots]
      exact count_roots_charTwoFrobeniusPolynomial_sq x
    have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 2 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x
              ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
        _ = 2 := hrootL
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 2 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_zero_of_value_eq ha hvalue]

private lemma superMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (superMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (superMinusOneGCD W).roots) =
        (superMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (superMinusOneGCD W).roots) (by simp))
  calc
    (superMinusOneGCD W).natDegree =
        (superMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (superMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_superMinusOneGCD W x

private lemma superMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) =
      2 * Nat.card F := by
  rw [superMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) +
        Nat.card (charTwoFiber W.a₃ ((superH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two W.a₃ _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma superMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneNumerator W / superMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  have hN := superMinusOneNumerator_ne_zero W
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : superMinusOneGCD W *
      (superMinusOneNumerator W / superMinusOneGCD W) =
        superMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : superMinusOneNumerator W / superMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, superMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := superMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_superMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact superMinusOneQuotient_natDegree W

private lemma superD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := superPoint_neg_one_eq_some W
  unfold superD
  rw [hpoint]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0))).natDegree = _
  rw [superX_negPZero_add_Q W]
  rw [num_natDegree_superMinusOneRat W]
  exact (superPointCount_eq_fiber_sum W).symm

private def superNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + (C (W.a₄ ^ 2) * g ^ 2 +
    C (W.a₃ ^ 2) * g * (X * g + f))

private def superNeighborSecond (W : WeierstrassCurve F) (g : F[X]) : F[X] :=
  C (W.a₃ ^ 2) * g ^ 2

private lemma super_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (superTwist W).toAffine.Nonsingular x y}
    {hMinus : (superTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (superTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (superTwist W).toAffine.Point) + superQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (superTwist W).toAffine.Point) - superQ W)
    (hdegree : x.denom.natDegree < x.num.natDegree)
    (hdegreeMinus : xMinus.denom.natDegree < xMinus.num.natDegree)
    (hdegreePlus : xPlus.denom.natDegree < xPlus.num.natDegree) :
    xMinus.num.natDegree + xPlus.num.natDegree =
      2 * x.num.natDegree + 2 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X y 0) := hplusEq.1
  have hneg : (superTwist W).toAffine.Nonsingular x
      ((superTwist W).toAffine.negY x y) :=
    ((superTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (superTwist W).toAffine.Point) - superQ W =
    -(-(.some x y hxy : (superTwist W).toAffine.Point) + superQ W) by
      abel] at hminusEq
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X
          ((superTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : xPlus = (y / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxPlus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, superTwist, zero_mul,
      add_zero, sub_eq_add_neg, CharTwo.neg_eq]
  have hrMinus : xMinus =
      ((y + RatFunc.C W.a₃) / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxMinus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      superTwist, zero_mul, add_zero, sub_eq_add_neg,
      CharTwo.neg_eq]
  have heq := super_coordinates_equation W hxy
  have hdiff : RatFunc.X + x ≠ 0 := by
    intro hzero
    apply hxQ
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
  have hpairProd := super_neighbor_pair_product W heq hdiff
  have hpairSum := super_neighbor_pair_sum W (s := y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (superNeighborFirst W x.num x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus * xPlus := by
    rw [superNeighborFirst_ratio]
    calc
      _ = xPlus * xMinus := hpairProd.symm
      _ = xMinus * xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F) (superNeighborSecond W x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus + xPlus := by
    rw [superNeighborSecond_ratio]
    calc
      _ = xPlus + xMinus := hpairSum.symm
      _ = xMinus + xPlus := by ring
  have hpoly : X * x.denom + x.num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := superNeighbor_primitive W
    (RatFunc.isCoprime_num_denom x) hpoly
  have hout : neighborDenominator x.num x.denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := superNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma superD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma superD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private def superDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C (W.a₄ ^ 2)

private def superDoubleDenominator (W : WeierstrassCurve F) : F[X] :=
  C (W.a₃ ^ 2)

private lemma superD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
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

private lemma superD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
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

private lemma superD_recurrence [Finite F] [CharP F 2]
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

private lemma supersingular_degree_computation [Finite F] [CharP F 2]
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
