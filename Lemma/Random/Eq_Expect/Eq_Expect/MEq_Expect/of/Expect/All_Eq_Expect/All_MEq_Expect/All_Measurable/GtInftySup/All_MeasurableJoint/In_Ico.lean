import Lemma.Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
import Lemma.Random.MeasurableJoint.is.Measurable.Measurable
import Lemma.Random.MEqCondExp_Integral.of.Integrable.Measurable
import Lemma.Random.Eq.of.Ne_0.MEq
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import sympy.concrete.sup
open MeasureTheory ProbabilityTheory


/--
Bellman equations with a finite state space and a general (e.g. continuous) action space.
`V` is the event-conditioned expected return `𝔼[… | s t = x]` (atoms of `s t`, as in
`Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico`);
`Q` is the σ-algebra conditional expected return `𝔼[… | s t, a t]` (`=ᵐ[π]`, as in
`Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico`).
The `V`-identities are read off on atoms of `s t` (`Random.MEqCondExp_Integral.of.Integrable.Measurable`,
`Random.Eq.of.Ne_0.MEq`); the `Q`-identity stays almost sure. Both sides of an event identity are `0` on
atoms of probability `0`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A]
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
  (h₃ : ∀ t x, Measurable (Q t x))
  (h₄ : ∀ t, Q t (s t) (a t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t, a t))
  (h₅ : ∀ t («s.bvar» : ℕ → S), V t («s.bvar» t) = 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₆ : 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | s t, a t, s (t + 1)) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | s (t + 1)))
  («s.bvar» : ℕ → S) :
-- imply
  V t («s.bvar» t) = 𝔼[a: π](Q t («s.bvar» t) (a t) | s t = «s.bvar» t) ∧
    V t («s.bvar» t) = 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t = «s.bvar» t) ∧
    Q t (s t) (a t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t, a t) := by
-- proof
  set x := «s.bvar» t
  have hrm : ∀ n, Measurable (r n) := fun n ↦ (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).1
  have hsm : ∀ n, Measurable (s n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).1
  have ham : ∀ n, Measurable (a n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).2
  have hpR : Measurable (fun ω t ↦ r t ω) := measurable_pi_lambda _ hrm
  have hpa : Measurable (fun ω t ↦ a t ω) := measurable_pi_lambda _ ham
  have hpr : Measurable (fun ω t ↦ r t ω, fun ω t ↦ s t ω) :=
    (measurable_pi_lambda _ hrm).prodMk (measurable_pi_lambda _ hsm)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t ↦
    Measurable.tsum fun k ↦ (measurable_pi_apply (t + k)).const_mul _
  have hf : Measurable (fun integ : (ℕ → ℝ) × (ℕ → S) ↦ integ.1 t + γ * V (t + 1) (integ.2 (t + 1))) :=
    ((measurable_pi_apply t).comp measurable_fst).add
      (((measurable_of_countable (V (t + 1))).comp ((measurable_pi_apply (t + 1)).comp measurable_snd)).const_mul γ)
  have hV : ∀ t y, V t y = ∫ ω, (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t:] ∂π[|s t ⁻¹' {y}] := by
    intro t y
    rw [h₅ t (fun _ ↦ y)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
  obtain ⟨R, hR⟩ := id h₂
  have hbd : ∀ t ω, |r t ω| ≤ R := fun t ω ↦ hR (Set.mem_range_self (t, ω))
  have hb : ∀ n ω k, ‖γ ^ k * r (n + k) ω‖ ≤ γ ^ k * |R| := fun n ω k ↦ by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hbd _ _).trans (le_abs_self R)) (pow_nonneg h₀.1 k)
  have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
  have hGi : ∀ n, Integrable (fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[n:]) π := fun n ↦
    Integrable.of_bound (Measurable.tsum fun k ↦ (hrm (n + k)).const_mul _).aestronglyMeasurable
      ((1 - γ)⁻¹ * |R|) (Filter.Eventually.of_forall fun ω ↦ tsum_of_norm_bounded hgeo (hb n ω))
  have h₅ae : ∀ t, V t (s t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t) := fun t ↦
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω ↦ hV t (s t ω))
      (Random.MEqCondExp_Integral.of.Integrable.Measurable (hsm t) (hGi t)).symm
  obtain ⟨h₈, h₉, h₁₀⟩ :=
    Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
      h₀ h₁ h₂ h₄ h₅ae h₆
  have hQi : Integrable (fun ω ↦ Q t (s t ω) (a t ω)) π := integrable_condExp.congr (h₄ t).symm
  have hri : Integrable (r t) π :=
    Integrable.of_bound (hrm t).aestronglyMeasurable |R|
      (Filter.Eventually.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le ((hbd t ω).trans (le_abs_self R)))
  have hVi : Integrable (fun ω ↦ V (t + 1) (s (t + 1) ω)) π := integrable_condExp.congr (h₅ae (t + 1)).symm
  have hF : Integrable (fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) π := hri.add (hVi.const_mul γ)
  have hx : ∀ {B : Set Ω} (f : Ω → ℝ), π B = 0 → ∫ ω, f ω ∂π[|B] = 0 :=
    fun f h ↦ by rw [cond_eq_zero_of_meas_eq_zero h, integral_zero_measure]
  refine ⟨?_, ?_, h₁₀⟩
  · simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpa.aemeasurable
      (show Measurable fun integ : ℕ → A ↦ Q t x (integ t) from (h₃ t x).comp (measurable_pi_apply t))]
    if h : π (s t ⁻¹' {x}) = 0 then
      rw [hV, hx _ h, hx _ h]
    else
      rw [Random.Eq.of.Ne_0.MEq (u := V t) (v := fun y ↦ ∫ ω, Q t (s t ω) (a t ω) ∂π[|s t ⁻¹' {y}])
        (h₈.trans (Random.MEqCondExp_Integral.of.Integrable.Measurable (hsm t) hQi)) h]
      exact integral_congr_ae ((ae_cond_mem (hsm t (measurableSet_singleton x))).mono fun ω hω ↦ by
        dsimp only
        rw [show s t ω = x from hω])
  · simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpr.aemeasurable hf]
    if h : π (s t ⁻¹' {x}) = 0 then
      rw [hV, hx _ h, hx _ h]
    else
      exact Random.Eq.of.Ne_0.MEq (u := V t)
        (v := fun y ↦ ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂π[|s t ⁻¹' {y}])
        (h₉.trans (Random.MEqCondExp_Integral.of.Integrable.Measurable (hsm t) hF)) h


-- created on 2026-10-06
