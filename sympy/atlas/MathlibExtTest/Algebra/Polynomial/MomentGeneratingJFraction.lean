/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/MomentGeneratingJFraction.lean -/


import sympy.atlas.Algebra.Polynomial.MomentGeneratingJFraction
import Lemma.Int.Polynomial.MomentGeneratingJFraction

namespace MetaMathlibExt

example (p : ℕ → Polynomial ℝ) (L : Polynomial ℝ →ₗ[ℝ] ℝ) (α β μ : ℕ → ℝ)
    (h0 : p 0 = 1) (h1 : p 1 = Polynomial.X - Polynomial.C (α 0))
    (hrec : ∀ n : ℕ, 1 ≤ n → p (n + 1) =
      (Polynomial.X - Polynomial.C (α n)) * p n - Polynomial.C (β n) * p (n - 1))
    (hμ : ∀ k : ℕ, μ k = L (Polynomial.X ^ k))
    (hLp : ∀ n : ℕ, 1 ≤ n → L (p n) = 0) :
    ∃ S : ℕ → PowerSeries ℝ, HasJacobiFraction μ α β (μ 0) S :=
  (moment_generating_function_as_J_fraction_general p L α β μ h0 h1 hrec hμ hLp).imp
    fun _ h => h.2

end MetaMathlibExt
