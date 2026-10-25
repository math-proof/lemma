import Mathlib
import sympy.Basic
import Lemma.FormalGroup.NSeries
import Lemma.FormalGroup.DrinfeldBasis
import Lemma.WeierstrassCurve.FormalGroupLaw
import Lemma.WeierstrassCurve.FormalGroup
import Def.WeierstrassCurve_HasseInvariant
import Def.FormalGroup_PointTransport
import Lemma.Int.P2MUtil

open FormalGroup
open PowerSeries
open WeierstrassCurve

/--
[WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom.lean)
-/

private lemma  eq_subst_formalW_of_constantCoeff_eq_zero
    {R : Type*}
    [CommRing R]
    (W : WeierstrassCurve R)
    {c : R⟦X⟧} (hc : constantCoeff c = 0)
    {u : R⟦X⟧} (hu : constantCoeff u = 0)
    (heq : u = c ^ 3 + C W.a₁ * c * u + C W.a₂ * c ^ 2 * u
      + C W.a₃ * u ^ 2 + C W.a₄ * c * u ^ 2 + C W.a₆ * u ^ 3) :
    u = PowerSeries.subst c W.formalW := by
  have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero' hc
  set v : R⟦X⟧ := PowerSeries.subst c W.formalW with hv

  have hveq : v = c ^ 3 + C W.a₁ * c * v + C W.a₂ * c ^ 2 * v
      + C W.a₃ * v ^ 2 + C W.a₄ * c * v ^ 2 + C W.a₆ * v ^ 3 := by
    have h := congrArg (PowerSeries.substAlgHom (R := R) hcs) W.formalW_eq
    simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
    rw [hv]
    exact h

  have hvc : constantCoeff v = 0 := by
    rw [hv]
    exact PowerSeries.constantCoeff_subst_eq_zero hc W.formalW W.constantCoeff_formalW

  set M : R⟦X⟧ :=
    C W.a₁ * c + C W.a₂ * c ^ 2 + C W.a₃ * (u + v)
      + C W.a₄ * c * (u + v) + C W.a₆ * (u ^ 2 + u * v + v ^ 2) with hM
  have hMδ : (1 - M) * (u - v) = 0 := by
    rw [hM]
    linear_combination heq - hveq
  have hMconst : constantCoeff (1 - M) = 1 := by
    rw [hM]
    simp [map_sub, map_add, map_mul, map_pow, hc, hu, hvc]
  have hunit : IsUnit (1 - M) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hMconst]
    exact isUnit_one
  have hδ : u - v = 0 := (IsUnit.mul_right_eq_zero hunit).mp hMδ
  exact sub_eq_zero.mp hδ

private lemma  constantCoeff_fgInvDenom
  {R : Type*}
  [CommRing R]
  (W : WeierstrassCurve R)
  : constantCoeff W.fgInvDenom = 1 := by
  simp only [fgInvDenom, map_sub, map_mul, map_one, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, W.constantCoeff_formalW, mul_zero, sub_zero]

private lemma  fgInvDenom_mul_invOfUnit
    {R : Type*}
    [CommRing R]
    (W : WeierstrassCurve R)
    :
    W.fgInvDenom * PowerSeries.invOfUnit W.fgInvDenom 1 = 1 :=
  PowerSeries.mul_invOfUnit W.fgInvDenom 1 (by rw [constantCoeff_fgInvDenom W]; simp)

private lemma  neg_formalW_mul_invOfUnit_eq_chart
    {R : Type*}
    [CommRing R]
    (W : WeierstrassCurve R)
    :
    (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1)
      = W.fgInv ^ 3 + C W.a₁ * W.fgInv * (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1)
        + C W.a₂ * W.fgInv ^ 2 * (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1)
        + C W.a₃ * (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1) ^ 2
        + C W.a₄ * W.fgInv * (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1) ^ 2
        + C W.a₆ * (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1) ^ 3 := by
  set E : R⟦X⟧ := PowerSeries.invOfUnit W.fgInvDenom 1 with hE
  set w : R⟦X⟧ := W.formalW with hw
  have hDE : (1 - C W.a₁ * X - C W.a₃ * w) * E = 1 := by
    have h := fgInvDenom_mul_invOfUnit W
    rwa [show W.fgInvDenom = 1 - C W.a₁ * X - C W.a₃ * w from rfl] at h
  have hweq := W.formalW_eq
  rw [← hw] at hweq
  rw [show W.fgInv = -X * E from rfl]
  linear_combination (-E ^ 3) * hweq
    + (w * E * (1 + (1 - C W.a₁ * X - C W.a₃ * w) * E) + C W.a₁ * X * w * E ^ 2
        + C W.a₃ * w ^ 2 * E ^ 2) * hDE

private lemma  subst_fgInv_formalW_mul_fgInvDenom'
    {R : Type*}
    [CommRing R]
    (W : WeierstrassCurve R)
    :
    PowerSeries.subst W.fgInv W.formalW * W.fgInvDenom = -W.formalW := by
  have hu : constantCoeff (-W.formalW * PowerSeries.invOfUnit W.fgInvDenom 1) = 0 := by
    simp [map_mul, map_neg, W.constantCoeff_formalW]
  have hfix := eq_subst_formalW_of_constantCoeff_eq_zero W W.constantCoeff_fgInv hu
    (neg_formalW_mul_invOfUnit_eq_chart W)
  rw [← hfix, mul_assoc, mul_comm (PowerSeries.invOfUnit W.fgInvDenom 1) W.fgInvDenom,
    fgInvDenom_mul_invOfUnit W, neg_mul, mul_one]
@[path]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R} :
-- imply
  PowerSeries.subst W.fgInv W.formalW * W.fgInvDenom = -W.formalW :=
-- proof
  subst_fgInv_formalW_mul_fgInvDenom' W


-- created on 2026-10-23
