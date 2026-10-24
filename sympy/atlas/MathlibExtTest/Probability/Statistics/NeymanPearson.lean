/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/Statistics/NeymanPearson.lean -/


import Lemma.Measure.Statistics.NeymanPearson

/-!
# Tests for the Neyman–Pearson lemma (dominated two-simple-hypothesis form)
-/


open MeasureTheory MathlibExt.Probability.Statistics.NeymanPearson

/-- The exact former Wanted statement follows from the stronger public theorem:
normalization of `p` and `q` and the fixed tie value are unused. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p q : Ω → ℝ}
    (hp_meas : Measurable p) (hq_meas : Measurable q)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_int : Integrable p μ) (hq_int : Integrable q μ)
    (_hp_prob : ∫ x, p x ∂μ = 1)
    (_hq_prob : ∫ x, q x ∂μ = 1)
    (k : ℝ) (hk : 0 ≤ k)
    (_γ : Set.Icc (0 : ℝ) 1)
    (φstar : Ω → Set.Icc (0 : ℝ) 1) (hφstar_meas : Measurable φstar)
    (hφstar_gt : ∀ x, k * p x < q x → (φstar x).val = 1)
    (hφstar_lt : ∀ x, q x < k * p x → (φstar x).val = 0)
    (_hφstar_eq : ∀ x, q x = k * p x → φstar x = _γ) :
    ∀ (φ : Ω → Set.Icc (0 : ℝ) 1), Measurable φ →
      (∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (φstar x).val * p x ∂μ) →
      (∫ x, (φ x).val * q x ∂μ ≤ ∫ x, (φstar x).val * q x ∂μ) :=
  neyman_pearson_dominated_two_simple hp_meas hq_meas hp_nonneg hq_nonneg
    hp_int hq_int k hk φstar hφstar_meas hφstar_gt hφstar_lt

/-- Boundary case `k = 0`: the constant-one test meets the threshold description
(the `q < 0` branch is vacuous for nonnegative `q`) and is most powerful. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p q : Ω → ℝ}
    (hp_meas : Measurable p) (hq_meas : Measurable q)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_int : Integrable p μ) (hq_int : Integrable q μ) :
    ∀ (φ : Ω → Set.Icc (0 : ℝ) 1), Measurable φ →
      (∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (1 : ℝ) * p x ∂μ) →
      (∫ x, (φ x).val * q x ∂μ ≤ ∫ x, (1 : ℝ) * q x ∂μ) := by
  intro φ hφ_meas hsize
  let φstar : Ω → Set.Icc (0 : ℝ) 1 := fun _ => ⟨1, by simp⟩
  have hφstar_meas : Measurable φstar := measurable_const
  have hgt : ∀ x, (0 : ℝ) * p x < q x → (φstar x).val = 1 := fun _ _ => rfl
  have hlt : ∀ x, q x < (0 : ℝ) * p x → (φstar x).val = 0 := by
    intro x hx
    rw [zero_mul] at hx
    exact absurd hx (not_lt_of_ge (hq_nonneg x))
  have hpow := neyman_pearson_dominated_two_simple hp_meas hq_meas hp_nonneg
    hq_nonneg hp_int hq_int (0 : ℝ) le_rfl φstar hφstar_meas hgt hlt
    φ hφ_meas
  have hsize' : ∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (φstar x).val * p x ∂μ := hsize
  have hconc := hpow hsize'
  simpa [φstar] using hconc
