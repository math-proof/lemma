import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_EllipticCurve_PointReduction
import Lemma.Int.P2MUtil
open Int
open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum


/--
[WeierstrassCurve_reducePoint_some](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_reducePoint_some.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve K} [W.HasGoodReduction R]
  {x y : K}
-- given
  (h : W.toAffine.Nonsingular x y)
  (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1)
  (hy : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
-- imply
  ∃ h', WeierstrassCurve.reducePoint_alt R W (.some x y h) =
    .some (WeierstrassCurve.reduceCoord R x) (WeierstrassCurve.reduceCoord R y) h' := by
-- proof
  obtain ⟨rx, hrx⟩ := exists_lift_of_le_one hx
  obtain ⟨ry, hry⟩ := exists_lift_of_le_one hy
  have hex : ∃ r : R, algebraMap R K r = x := ⟨rx, hrx⟩
  have hey : ∃ r : R, algebraMap R K r = y := ⟨ry, hry⟩
  have hcx : reduceCoord R x = residue R rx := by
    rw [reduceCoord, dite_eq_left hex]
    exact congrArg _ (IsFractionRing.injective R K (hex.choose_spec.trans hrx.symm))
  have hcy : reduceCoord R y = residue R ry := by
    rw [reduceCoord, dite_eq_left hey]
    exact congrArg _ (IsFractionRing.injective R K (hey.choose_spec.trans hry.symm))
  have heqK : ((integralModel R W).map (algebraMap R K)).toAffine.Equation
      (algebraMap R K rx) (algebraMap R K ry) := by
    have hbc : (integralModel R W).map (algebraMap R K) = W := baseChange_integralModel_eq R W
    rw [hbc, hrx, hry]
    exact h.1
  have heqR : (integralModel R W).toAffine.Equation rx ry :=
    (Affine.map_equation _ (IsFractionRing.injective R K) _ _).mp heqK
  have heqk : (reduction R W).toAffine.Equation (residue R rx) (residue R ry) :=
    heqR.map (residue R)
  have hell : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp ‹W.HasGoodReduction R›
  have hns : (reduction R W).toAffine.Nonsingular (reduceCoord R x) (reduceCoord R y) := by
    rw [hcx, hcy]
    exact Affine.equation_iff_nonsingular.mp heqk
  have hxy :
      valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 ∧
        valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 := ⟨hx, hy⟩
  refine ⟨hns, ?_⟩
  simp only [reducePoint_alt, dite_eq_left hxy, dite_eq_left hns]


-- created on 2026-10-24
