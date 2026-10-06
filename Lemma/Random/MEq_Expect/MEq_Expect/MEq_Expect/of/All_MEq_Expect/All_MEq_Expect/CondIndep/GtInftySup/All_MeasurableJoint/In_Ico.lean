import Lemma.Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
import Lemma.Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
import Lemma.Random.MeasurableJoint.is.Measurable.Measurable
import sympy.concrete.sup
open MeasureTheory ProbabilityTheory


/--
Bellman equations on general state / action spaces with the Markov property stated as conditional
independence: given `s[t+1]`, the future reward path `r[t+1:]` is independent of `(s[t], a[t])`
(`h₃ : r[t + 1:] ⟂ᵢ[π] (s t, a t) | s (t + 1)`, Mathlib's `CondIndepFun`, which needs `StandardBorelSpace Ω`).
Corollary of
`Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico`,
whose `h₅` (`𝔼[… | s t, a t, s (t + 1)] =ᵐ 𝔼[… | s (t + 1)]`) follows from conditional independence by
`Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {r : ℕ → Ω → ℝ}
  {γ : ℝ}
  {t : ℕ}
  {Q : ℕ → S → A → ℝ}
  {V : ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, Measurable (r t, s t, a t)) -- joint random variables r, s, a
  (h₂ : sup[t, ω] |r t ω| < ∞)
  (h₃ : r[t + 1:] ⟂ᵢ[π] (s t, a t) | s (t + 1))
  (h₄ : ∀ t, Q t (s t) (a t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t, a t))
  (h₅ : ∀ t, V t (s t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t)) :
-- imply
  V t (s t) =ᵐ[π] 𝔼[s, a: π](Q t (s t) (a t) | s t) ∧
    V t (s t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t) ∧
    Q t (s t) (a t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t, a t) := by
-- proof
  apply Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
    h₀ h₁ h₂ h₄ h₅
  have hrm : ∀ n, Measurable (r n) := fun n ↦ (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).1
  have hsm : ∀ n, Measurable (s n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).1
  have ham : ∀ n, Measurable (a n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).2
  -- the reward path `r[t + 1:]` and the discounted return functional `γ ** Stack[k](k) @ ·`
  have hF : Measurable (Expectation.asRV r[t + 1:]) := measurable_pi_lambda _ fun k ↦ hrm (t + 1 + k)
  have hg : Measurable fun p : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ p :=
    Measurable.tsum fun k ↦ (measurable_pi_apply k).const_mul _
  obtain ⟨R, hR⟩ := id h₂
  have hr : ∀ t ω, |r t ω| ≤ R := fun t ω ↦ hR (Set.mem_range_self (t, ω))
  have hb : ∀ ω k, ‖γ ^ k * r (t + 1 + k) ω‖ ≤ γ ^ k * |R| := fun ω k ↦ by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hr _ _).trans (le_abs_self R)) (pow_nonneg h₀.1 k)
  have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
  have hint : Integrable (fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ Expectation.asRV r[t + 1:] ω) π :=
    Integrable.of_bound (hg.comp hF).aestronglyMeasurable ((1 - γ)⁻¹ * |R|)
      (Filter.Eventually.of_forall fun ω ↦ tsum_of_norm_bounded hgeo (hb ω))
  have h := Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
    (X := JointRandomSymbol (s t) (a t)) hF (Random.MeasurableJoint.of.Measurable.Measurable (hsm t) (ham t)) (hsm (t + 1)) hg hint h₃
  -- repack the conditioning `((s t, a t), s (t + 1))` as `(s t, (a t, s (t + 1)))`
  have hσ : MeasurableSpace.comap (JointRandomSymbol (JointRandomSymbol (s t) (a t)) (s (t + 1))) inferInstance =
      MeasurableSpace.comap (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))) inferInstance := by
    apply le_antisymm
    · apply Measurable.comap_le
      exact (show Measurable fun p : S × A × S ↦ ((p.1, p.2.1), p.2.2) by fun_prop).comp
        (comap_measurable (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))))
    · apply Measurable.comap_le
      exact (show Measurable fun p : (S × A) × S ↦ (p.1.1, p.1.2, p.2) by fun_prop).comp
        (comap_measurable (JointRandomSymbol (JointRandomSymbol (s t) (a t)) (s (t + 1))))
  show π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ Expectation.asRV r[t + 1:] ω) |
      MeasurableSpace.comap (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))) inferInstance] =ᵐ[π]
    π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ Expectation.asRV r[t + 1:] ω) | MeasurableSpace.comap (s (t + 1)) inferInstance]
  rw [← hσ]
  exact h


-- created on 2026-10-06
