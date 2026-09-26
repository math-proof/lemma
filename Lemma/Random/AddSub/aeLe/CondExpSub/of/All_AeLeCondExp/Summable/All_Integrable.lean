import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}
  {f : ℕ → Ω → ℝ}
  {T : ℕ → ℝ}
  {C : ℝ}
-- given
  (h₀ : ∀ n, Integrable (f n) μ)
  (h₁ : Summable fun n => T n ^ 2)
  (h₂ : ∀ n, μ[f (n + 1) | ℱ n] ≤ᵐ[μ] fun ω => (1 - T n) * f n ω + C * T n ^ 2)
  (n : ℕ) :
-- imply
  (fun ω => -f n ω - C * ∑' k, T (k + n) ^ 2 + T n * f n ω) ≤ᵐ[μ] μ[fun ω => -f (n + 1) ω - C * ∑' k, T (k + (n + 1)) ^ 2 | ℱ n] := by
-- proof
  have htail : ∑' k, T (k + n) ^ 2 = T n ^ 2 + ∑' k, T (k + (n + 1)) ^ 2 := by
    rw [((summable_nat_add_iff n).2 h₁).tsum_eq_zero_add, zero_add]
    congr 2
    ext k
    ring_nf
  have hc : μ[-f (n + 1) - fun _ => C * ∑' k, T (k + (n + 1)) ^ 2 | ℱ n] =ᵐ[μ] -μ[f (n + 1) | ℱ n] - fun _ => C * ∑' k, T (k + (n + 1)) ^ 2 := by
    filter_upwards [condExp_sub (m := ℱ n) (h₀ (n + 1)).neg (integrable_const (C * ∑' k, T (k + (n + 1)) ^ 2)), condExp_neg (m := ℱ n) (μ := μ) (f (n + 1))] with ω h₃ h₄
    rw [h₃, Pi.sub_apply, h₄, condExp_const (ℱ.le n)]
    rfl
  filter_upwards [hc, h₂ n] with ω h₃ h₄
  simp only [Pi.sub_apply, Pi.neg_apply] at h₃
  rw [show (fun ω => -f (n + 1) ω - C * ∑' k, T (k + (n + 1)) ^ 2) = -f (n + 1) - fun _ => C * ∑' k, T (k + (n + 1)) ^ 2 from rfl, h₃, htail]
  linarith


-- created on 2026-09-26