import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Isogeny.ConditionalCurrency
import Lemma.Int.P2MUtil
open Int
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve


/--
[WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean)
-/
@[path]
private lemma main
  {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
  {D : IsogenyEndDatum W}
  {P : W.Point}
-- given
  (hN : NormFormulaAlong F D.ι D.hfin) :
-- imply
  D.pointEnd hN P =
    (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) -
      (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by
-- proof
  set Q : W.Point := (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) with hQ
  set Q₀ : W.Point :=
    (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F W.FunctionField) =
      Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι, hP, h0]
  rw [IsogenyEndDatum.pointEnd_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]


-- created on 2026-10-24
