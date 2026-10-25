/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/LaplaceTheta.lean -/

import Def.NumberTheory.PrimeCounting.LaplaceTheta
import Lemma.Nat.PrimeCounting.LaplaceTheta


/-!
# Tests for the Laplace transform of `theta (exp ·)`.
-/

-- Definitional expansion of `primeLogSeries`.
example (s : ℂ) : Chebyshev.primeLogSeries s =
    ∑' p : Nat.Primes, (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s) := by
  rfl

-- Identity at generic `s` with `1 < s.re`.
example (s : ℂ) (hs : 1 < s.re) :
    laplace (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ)) s =
      Chebyshev.primeLogSeries s / s :=
  Chebyshev.laplace_theta_exp_eq_primeLogSeries_div s hs

-- `HasLaplace` at generic `s`.
example (s : ℂ) (hs : 1 < s.re) :
    HasLaplace (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ)) s
      (Chebyshev.primeLogSeries s / s) :=
  Chebyshev.hasLaplace_theta_exp s hs

-- Concrete convergence and value at `s = 2`.
example : HasLaplace (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ))
    (2 : ℂ) (Chebyshev.primeLogSeries 2 / 2) := by
  have h2 : ((2 : ℂ)).re = 2 := by simp
  have hs : 1 < ((2 : ℂ)).re := by rw [h2]; norm_num
  exact Chebyshev.hasLaplace_theta_exp _ hs

-- Exact holomorphy statement.
example : DifferentiableOn ℂ
    (laplace (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ)))
    {s | 1 < s.re} :=
  Chebyshev.differentiableOn_laplace_theta_exp

