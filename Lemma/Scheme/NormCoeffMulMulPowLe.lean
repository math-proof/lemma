import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma l1_M_nonneg
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F : PowerSeries L)
  {ρ M : ℝ}
  -- given
  (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) :
  -- imply
  0 ≤ M := by
  -- proof
  have := hF 0
  simp only [pow_zero, mul_one] at this
  apply (norm_nonneg _).trans this

/--
[PowerSeries_norm_coeff_mul_mul_pow_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_norm_coeff_mul_mul_pow_le.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F G : PowerSeries L)
  {ρ M M' : ℝ}
  (n : ℕ)
  -- given
  (hρ : 0 ≤ ρ)
  (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
  (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M') :
  -- imply
  ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := by
  -- proof
  have hM := l1_M_nonneg F hF
  have hM' := l1_M_nonneg G hG
  rw [PowerSeries.coeff_mul]
  obtain h0 | hpos := (pow_nonneg hρ n).eq_or_lt
  ·
    rw [← h0, mul_zero]
    apply mul_nonneg hM hM'
  have hC : 0 ≤ M * M' / ρ ^ n := div_nonneg (mul_nonneg hM hM') hpos.le
  have h : ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ ≤
    M * M' / ρ ^ n := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [norm_mul, le_div_iff₀ hpos, ← hp, pow_add]
    calc
      _ = (‖PowerSeries.coeff p.1 F‖ * ρ ^ p.1) * (‖PowerSeries.coeff p.2 G‖ * ρ ^ p.2) := by
        ring
      _ ≤ M * M' := mul_le_mul (hF p.1) (hG p.2) (by positivity) hM
  refine (le_div_iff₀ hpos).mp h


-- created on 2026-10-20
