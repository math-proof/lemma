import Mathlib
import sympy.Basic


/--
py claimed the Taylor identity `f(x) = ∑ (x-a)^n / n! * f⁽ⁿ⁾(a)` for every differentiable `f`.
It is false without analyticity: flat functions (e.g. `exp(-1/x²)` at `0`) have zero Taylor
series but are nonzero. We assume `f` admits a power series on a ball of extended radius `r > 0`
centered at `a`, and that `x` lies inside that ball.
-/
@[path]
private lemma main
  {f : ℝ → ℝ}
  {p : FormalMultilinearSeries ℝ ℝ ℝ}
  {a : ℝ}
  {r : ENNReal}
  {x : ℝ}
-- given
  (h : HasFPowerSeriesOnBall f p a r)
  (hx : x - a ∈ Metric.eball (0 : ℝ) r) :
-- imply
  f x = ∑' n, (x - a) ^ n / (Nat.factorial n : ℝ) * iteratedDeriv n f a := by
-- proof
  have hs := h.hasSum_iteratedFDeriv (y := x - a) hx
  have heq : (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℝ n f a fun _ : Fin n => x - a) =
      fun n => (x - a) ^ n / (Nat.factorial n : ℝ) * iteratedDeriv n f a := by
    funext n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp [Finset.prod_const, Fintype.card_fin, div_eq_mul_inv]
    ring
  rw [heq, show a + (x - a) = x by ring] at hs
  simpa using hs.tsum_eq.symm


-- created on 2026-10-10
