import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_abv_eval_le_gaussNorm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_abv_eval_le_gaussNorm.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {v : AbsoluteValue R ℝ}
  {c : ℝ}
  {p : R[X]}
  {z : R}
-- given
  (hv : IsNonarchimedean v)
  (hc : 0 ≤ c)
  (hz : v z ≤ c) :
-- imply
  v (p.eval z) ≤ p.gaussNorm v c := by
-- proof
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp [Subsingleton.elim p 0]
  rw [Polynomial.eval_eq_sum_range]
  obtain ⟨j, -, hj⟩ := IsNonarchimedean.finset_image_add_of_nonempty hv
    (fun i => p.coeff i * z ^ i) Finset.nonempty_range_add_one
  calc v (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i)
      ≤ v (p.coeff j * z ^ j) := hj
    _ = v (p.coeff j) * v z ^ j := by rw [map_mul, map_pow]
    _ ≤ v (p.coeff j) * c ^ j := by gcongr
    _ ≤ p.gaussNorm v c := p.le_gaussNorm v hc j


-- created on 2026-10-05
