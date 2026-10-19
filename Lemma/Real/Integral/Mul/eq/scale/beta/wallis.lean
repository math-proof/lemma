import Lemma.Real.Integral.Mul.eq.Div.gamma.wallis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
open Real


/--
The beta form of the Wallis integral. Mathlib has no real `beta` function; `Β(m/2, n/2)` is the
Gamma quotient, so `∫ = Β(m/2, n/2) / 2` is the Gamma identity at `m = 1`.
-/
@[path]
private lemma main
  {m n : ℕ}
  (h₀ : 0 < n)
  (h₁ : m = 1) :
-- imply
  (∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x ^ (m - 1) * Real.sin x ^ (n - 1)) = (Real.Gamma ((m : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) / Real.Gamma (((m + n : ℕ) : ℝ) / 2)) / 2 := by
-- proof
  rw [Integral.Mul.eq.Div.gamma.wallis (m := m) (n := n) h₀ h₁]
  ring


-- created on 2026-10-11
-- updated on 2026-10-17
