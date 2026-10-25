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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part2
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

lemma delta_eq_sixteen_mul_cubic_discr
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    W.Δ = 16 * (cubic W).discr := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, cubic_discr]
  ring

lemma cubic_discr_ne_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).discr ≠ 0 := by
  intro h
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  apply hΔ
  rw [delta_eq_sixteen_mul_cubic_discr, h, mul_zero]

lemma cubic_separable (W : WeierstrassCurve F)
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

lemma isCoprime_cubic_duplicationNumerator
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

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
