/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/WeightedLargeSieve.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.WeightedLargeSieve
import Lemma.Nat.PrimeCounting.WeightedLargeSieve
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.PrimeCounting.WeightedLargeSieve

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Apply the weighted large sieve to two points and constant coefficients at length two.
example :
    let x : Fin 2 → ℝ := ![0, 1 / 2]
    let δ : Fin 2 → ℝ := fun _ ↦ 1 / 2
    let a : ℕ → ℂ := fun _ ↦ 1
    ∑ r, (2 + 3 / (2 * δ r))⁻¹ *
        ‖∑ n ∈ Finset.range 2, a n *
          Complex.exp (((2 * Real.pi * (n * x r) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ n ∈ Finset.range 2, ‖a n‖ ^ 2 := by
  dsimp only
  apply weightedLargeSieve
  · intro r
    norm_num
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact (hrs rfl).elim
    · norm_num [AddCircle.norm_eq]
    · norm_num [AddCircle.norm_eq]
    · exact (hrs rfl).elim

end MathlibExtTest.NumberTheory.PrimeCounting.WeightedLargeSieve
