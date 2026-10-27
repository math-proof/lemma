import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Isogeny.ConditionalCurrency
import Lemma.Int.P2MUtil
set_option maxHeartbeats 800000
open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine Int


private lemma inertiaDegAlong_eq_one_cf
  {F : Type v} [Field F] [DecidableEq F]
  {V W : Affine F}
  [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
  (ι : V.FunctionField →ₐ[F] W.FunctionField)
  (hι : ι.toRingHom.IsIntegral)
  (w : AlgebraicCurve.Place F W.FunctionField) :
  w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rwa [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h

private lemma pushforwardAlong_single_eq_cf
  {F : Type v} [Field F] [DecidableEq F]
  {V W : Affine F}
  [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
  (ι : V.FunctionField →ₐ[F] W.FunctionField)
  (hι : ι.toRingHom.IsIntegral)
  (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
  Divisor.pushforwardAlong ι hι (Finsupp.single w n) =
      Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one_cf ι hι w, Nat.cast_one, mul_one]

universe u
/--
[WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub.lean)
-/
@[path]
private lemma main
  {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
  {V₀ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
  {V₁ : WeierstrassCurve.Affine F} [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
  {φ : IsogenyHomDatum V₀ V₁}
  {P : V₀.Point}
-- given
  (hN : NormFormulaAlong F φ.ι φ.hfin) :
-- imply
  φ.pointHom hN P =
      (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι) -
        (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) := by
-- proof
  set Q : V₁.Point := (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι) with hQ
  set Q₀ : V₁.Point :=
    (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong φ.ι φ.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero φ.ι φ.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F V₁.FunctionField) =
      Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq_cf φ.ι φ.hι, pushforwardAlong_single_eq_cf φ.ι φ.hι, hP, h0]
  have happ : φ.pointHom hN P =
      genusOnePic0Equiv V₁ (Pic0.pushforwardAlongHom φ.ι φ.hι φ.hfin hN (pointClass P)) := by
    rw [← genusOnePic0Equiv_symm_apply]
    rfl
  rw [happ, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]


-- created on 2026-10-24
