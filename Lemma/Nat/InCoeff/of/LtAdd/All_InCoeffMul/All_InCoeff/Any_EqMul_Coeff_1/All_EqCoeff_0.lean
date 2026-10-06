import Mathlib
import sympy.Basic


/--
[PowerSeries_coeff_mem_subring_of_coeff_mul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean)
-/
@[main]
private lemma main
  [CommRing K]
  {R : Subring K}
  {P U : PowerSeries K}
  {m₀ L : ℕ}
  {n : ℕ}
-- given
  (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
  (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
  (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
  (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
  (hn : n + m₀ < L) :
-- imply
  PowerSeries.coeff n P ∈ R := by
-- proof
  obtain ⟨v, hv, hvu⟩ := hU₁
  induction n using Nat.strong_induction_on with
  | _ n ih =>

    have hsum := PowerSeries.coeff_mul (n + m₀) P U

    have hmem : (n, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n + m₀) := by simp
    rw [← Finset.add_sum_erase _ _ hmem] at hsum

    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U ∈ R := by
      refine Subring.sum_mem _ fun x hx => ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rcases lt_trichotomy x.1 n with hlt | heq | hgt
      · exact Subring.mul_mem _ (ih x.1 hlt (by omega)) (hU x.2)
      · exfalso; apply hne
        have : x.2 = m₀ := by omega
        exact Prod.ext heq this
      · have : x.2 < m₀ := by omega
        rw [hU₀ x.2 this, mul_zero]
        exact Subring.zero_mem _

    have hkey : PowerSeries.coeff n P = v * (PowerSeries.coeff (n + m₀) (P * U) -
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U) := by
      rw [hsum, add_sub_cancel_right, mul_comm v, mul_assoc, mul_comm _ v, hvu, mul_one]
    rw [hkey]
    exact Subring.mul_mem _ hv (Subring.sub_mem _ (hPU _ hn) hrest)


-- created on 2026-10-05
