import Lemma.Real.Integral.Sin.eq.Mul.gamma.wallis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
open Real


/--
Wallis' product integral at cosine power `0` (`m = 1`):
`∫ cos(x)^(m-1) sin(x)^(n-1) dx = Γ(m/2) Γ(n/2) / (2 Γ((m+n)/2))` on `(0, π/2)`.
-/
@[path]
private lemma main
  {m n : ℕ}
  (h₀ : 0 < n)
  (h₁ : m = 1) :
-- imply
  (∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x ^ (m - 1) * Real.sin x ^ (n - 1)) = Real.Gamma ((m : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) / (2 * Real.Gamma (((m + n : ℕ) : ℝ) / 2)) := by
-- proof
  subst h₁
  simp only [Nat.cast_one, Nat.sub_self, pow_zero, one_mul]
  rw [Integral.Sin.eq.Mul.gamma.wallis h₀, Real.Gamma_one_half_eq]
  have hden : (n : ℝ) / 2 + 1 / 2 = ((1 + n : ℕ) : ℝ) / 2 := by
    simp [Nat.cast_add, Nat.cast_one]
    ring
  rw [hden]


-- created on 2020-07-01
-- updated on 2026-10-17
