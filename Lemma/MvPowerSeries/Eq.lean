import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero.lean)
-/
@[path]
private lemma main
  {σ R : Type u} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x v v' : MvPowerSeries σ R)
  (hx : MvPowerSeries.constantCoeff x = 0) (hv : MvPowerSeries.constantCoeff v = 0)
  (hv' : MvPowerSeries.constantCoeff v' = 0)
  (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
  (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
  -- imply
  v = v' := by
  -- proof
  have key : (v - v') * (1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2)) = 0 := by
    linear_combination h - h'
  have hunit : IsUnit (1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp [hx, hv, hv']
  have := hunit.mul_left_eq_zero.mp key
  refine sub_eq_zero.mp this


-- created on 2026-10-20
