import Mathlib
import sympy.Basic
import sympy.Analysis.Asymptotics.CatalanAsymptoticExpansion

/--
[catalan_stirling_asymptotic_expansions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/CatalanAsymptoticExpansion.lean)
-/
@[path]
private lemma catalan_stirling_asymptotic_expansions_eq
-- given
  (E : ℕ → ℤ)
  (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
    (∑ j ∈ Finset.range (n / 2 + 1),
      (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) :
-- imply
  ((∀ m : ℕ,
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) ^ m *
          (Real.log
              ((catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
                (4 : ℝ) ^ n) -
            ∑ j ∈ Finset.range m,
              (-1 : ℝ) ^ (j + 2) *
                ((((2 : ℝ) ^ (j + 1))⁻¹ - 2) *
                    (bernoulli (j + 2) : ℝ) - (j + 1 : ℕ) - 1) /
                  ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                (1 / ((n : ℝ) ^ (j + 1)))))
      Filter.atTop (nhds 0)) ∧
  (∀ m : ℕ,
    Filter.Tendsto
      (fun n : ℕ =>
        (n + 3 / 4 : ℝ) ^ (2 * m) *
          (Real.log
              ((catalan n : ℝ) *
                  Real.sqrt (Real.pi * (n + 3 / 4 : ℝ) ^ 3) /
                (4 : ℝ) ^ n) -
            ∑ j ∈ Finset.range m,
              ((2 : ℝ) ^ (4 * (j + 1) + 2))⁻¹ *
                (4 - (E (2 * (j + 1)) : ℝ)) / (j + 1 : ℕ) *
                (1 / ((n + 3 / 4 : ℝ) ^ (2 * (j + 1))))))
      Filter.atTop (nhds 0))) :=
-- proof
  MetaMathlibExt.catalan_stirling_asymptotic_expansions E hE


-- created on 2026-10-09
