import Mathlib
import sympy.Basic

open IsLocalRing

/--
[WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] [IsLocalRing S]
  {a₁ a₂ a₃ a₄ a₆ x v v' : S}
-- given
  (hx : x ∈ maximalIdeal S)
  (hv : v ∈ maximalIdeal S)
  (hv' : v' ∈ maximalIdeal S)
  (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
  (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
-- imply
  v = v' := by
-- proof
  set B := 1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2) with hB
  have hprod : (v - v') * B = 0 := by rw [hB]; linear_combination h - h'
  have hBunit : IsUnit B := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hBm
    have h1 : B - 1 ∈ IsLocalRing.maximalIdeal S := by
      rw [hB]
      have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ a₁ hx)
        (Ideal.mul_mem_left _ a₃ (Ideal.add_mem _ hv hv')))
        (Submodule.neg_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (a₂ * x) hx)
          (Ideal.mul_mem_left _ (a₄ * x) (Ideal.add_mem _ hv hv')))
          (Ideal.mul_mem_left _ a₆ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ v hv) (Ideal.mul_mem_left _ v hv'))
            (Ideal.mul_mem_left _ v' hv')))))
      convert this using 1; ring
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ hBm h1; simp at this
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  exact sub_eq_zero.mp (hBunit.mul_left_eq_zero.mp hprod)


-- created on 2026-10-05
