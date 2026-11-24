module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part5
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/
namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma card_odd [Finite F] (hchar : ringChar F ≠ 2) : Odd (Nat.card F) := by
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

lemma twice_half_card_add_three [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 3) / 2) = Nat.card F + 3 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

lemma aeval_cubic_X_pow_card [Finite F] (W : WeierstrassCurve F) :
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

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
