/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/LogSum.lean -/


import Lemma.Real.LogSum

/-- Gibbs' inequality for probability vectors on a finset. -/
example {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 < q i) (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1) :
    0 ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  simpa [hps, hqs] using Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div s p q hp hq

/-- `p` may vanish on part of `s`: `p = (0, 1)` against `q = (1, 1)`. -/
example : Real.log (1 / 2) ≤ 0 := by
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ ![(0 : ℝ), 1] ![1, 1]
    (fun i _ => by fin_cases i <;> simp) (fun i _ => by fin_cases i <;> simp)
  simpa [one_add_one_eq_two] using h

/-- The empty finset is allowed: both sides are `0`. -/
example (p q : Fin 2 → ℝ)
    (hp : ∀ i ∈ (∅ : Finset (Fin 2)), 0 ≤ p i)
    (hq : ∀ i ∈ (∅ : Finset (Fin 2)), 0 < q i) :
    (∑ i ∈ (∅ : Finset (Fin 2)), p i) *
        Real.log ((∑ i ∈ (∅ : Finset (Fin 2)), p i) /
          (∑ i ∈ (∅ : Finset (Fin 2)), q i))
      ≤ ∑ i ∈ (∅ : Finset (Fin 2)), p i * Real.log (p i / q i) :=
  Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div ∅ p q hp hq
