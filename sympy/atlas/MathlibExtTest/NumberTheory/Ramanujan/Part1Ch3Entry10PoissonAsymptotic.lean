/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Entry10PoissonAsymptotic.lean -/


import sympy.atlas.Combinatorics.AssociatedStirlingSecond
import Lemma.Finset.AssociatedStirlingSecond
import Lemma.Nat.Ramanujan.Part1Ch3Entry10PoissonAsymptotic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10PoissonAsymptotic

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10PoissonAsymptotic

-- The frozen Entry 10 name inherits the canonical support bound through the public bridge.
example (n k : ℕ) (hnk : n < 2 * k) : twoAssocStirlingSecond n k = 0 := by
  rw [twoAssocStirlingSecond_eq_canonical]
  exact MetaMathlibExt.twoAssocStirlingSecond_eq_zero_of_lt_two_mul n k hnk

-- The public theorem applies directly from its documented growth hypotheses.
example (M : ℕ) (hM : 0 < M) (φ : ℝ → ℂ) (G : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (F : Finset ℕ)
    (h_poly : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p ∧ ‖G x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :=
  ramanujan_part1_ch3_entry10_poisson_asymptotic
    M hM φ G A hA F h_poly hG_ge h_deriv

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10PoissonAsymptotic
