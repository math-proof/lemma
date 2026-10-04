import Mathlib
import sympy.Basic


/--
[MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {τ : Type w}
  {M : Ideal R}
  {j : R}
  {g g' : MvPowerSeries τ R}
-- given
  (hj : ∀ m ∈ M, m * j = 0)
  (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
-- imply
  j • g = j • g' := by
-- proof
  refine MvPowerSeries.ext fun n => ?_
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul]
  have h0 : (MvPowerSeries.coeff n g - MvPowerSeries.coeff n g') * j = 0 := hj _ (h n)
  rw [sub_mul, sub_eq_zero] at h0
  rw [mul_comm, h0, mul_comm]


-- created on 2026-10-03
