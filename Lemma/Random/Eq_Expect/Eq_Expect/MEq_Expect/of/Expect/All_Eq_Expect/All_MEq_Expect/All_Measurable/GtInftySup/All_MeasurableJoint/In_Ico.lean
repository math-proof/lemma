import Lemma.Random.MEq_ExpectCond.MEq_ExpectCond.MEq_ExpectCond.of.MEqExpectS.All_MEq_ExpectCondDot.All_MEq_ExpectCondDot.GtInftySup.In_Ico
import Lemma.Random.MEqCondExp_Integral.of.Integrable.Measurable
import Lemma.Random.Eq.of.Ne_0.MEq
import Theorem.Probability.CondExpectation
import Theorem.Probability.JointRv.AsRV
open MeasureTheory ProbabilityTheory


/--
Bellman equations with a finite state space and a general (e.g. continuous) action space.
`V` is the regular (observation) form of the conditional expected return `𝔼[… | s t = x]`;
`Q` is the σ-algebra conditional expected return `𝔼[… | s t, a t]` (`=ᵐ[π]`, as in
`Random.MEq_ExpectCond.MEq_ExpectCond.MEq_ExpectCond.of.MEqExpectS.All_MEq_ExpectCondDot.All_MEq_ExpectCondDot.GtInftySup.In_Ico`).
The `V`-identities are read off on atoms of `s t` with positive mass
(`Random.MEqCondExp_Integral.of.Integrable.Measurable`,
`Random.Eq.of.Ne_0.MEq`); the `Q`-identity stays almost sure.
`V t (s t)` is a version of `𝔼[… | s t]` at every time (`condEval_comp_ae_eq_condSigma`).
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [Nonempty S]
  [StandardBorelSpace S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
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
  (h₄ : ∀ t, Q t (s t) (a t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t, a t))
  (h₅ : ∀ t («\sf{s}» : ℕ → S), V t («\sf{s}» t) = 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = «\sf{s}» t))
  (h₆ : 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t + 1:] | s t, a t, s (t + 1)) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t + 1:] | s (t + 1)))
  («\sf{s}» : ℕ → S) :
-- imply
  (π (s t ⁻¹' {«\sf{s}» t}) ≠ 0 →
      V t («\sf{s}» t) = 𝔼[a: π](Q t («\sf{s}» t) (a t) | s t = «\sf{s}» t)) ∧
    (π (s t ⁻¹' {«\sf{s}» t}) ≠ 0 →
      V t («\sf{s}» t) = 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t = «\sf{s}» t)) ∧
    Q t (s t) (a t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t, a t) := by
-- proof
  set x := «\sf{s}» t
  have hrm : ∀ n, Measurable (r n) := fun n ↦ (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).1
  have hsm : ∀ n, Measurable (s n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).1
  have ham : ∀ n, Measurable (a n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).2
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval hrm
  have hpa : Measurable (fun ω t ↦ a t ω) := Measurable.of_eval ham
  have hpr : Measurable (fun ω t ↦ r t ω, fun ω t ↦ s t ω) :=
    (Measurable.of_eval hrm).prodMk (Measurable.of_eval hsm)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := fun t ↦
    Measurable.tsum fun k ↦ (measurable_pi_apply (t + k)).const_mul _
  have hf : Measurable (fun integ : (ℕ → ℝ) × (ℕ → S) ↦ integ.1 t + γ * V (t + 1) (integ.2 (t + 1))) :=
    ((measurable_pi_apply t).comp measurable_fst).add
      (((measurable_of_countable (V (t + 1))).comp ((measurable_pi_apply (t + 1)).comp measurable_snd)).const_mul γ)
  obtain ⟨R, hR⟩ := id h₂
  have hbd : ∀ t ω, |r t ω| ≤ R := fun t ω ↦ hR (Set.mem_range_self (t, ω))
  have hb : ∀ n ω k, ‖γ ^ k * r (n + k) ω‖ ≤ γ ^ k * |R| := fun n ω k ↦ by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hbd _ _).trans (le_abs_self R)) (pow_nonneg h₀.1 k)
  have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
  have hGi : ∀ n, Integrable (fun ω ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (r · ω)[n:]) π := fun n ↦
    Integrable.of_bound (Measurable.tsum fun k ↦ (hrm (n + k)).const_mul _).aestronglyMeasurable
      ((1 - γ)⁻¹ * |R|) (Filter.Eventually.of_forall fun ω ↦ tsum_of_norm_bounded hgeo (hb n ω))
  have h₅ae : ∀ t, V t (s t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t) := fun t ↦ by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω n ↦ r n ω) (y := s t) (f := fun integ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:])
        hpR.aemeasurable (hsm t) (Measurable.stronglyMeasurable (hfG t)) (hGi t)
    filter_upwards [hcomp] with ω hω
    have hx := h₅ t (fun _ ↦ s t ω)
    simp only [Expectation.asRV_process] at hx hω ⊢
    exact hx.trans hω
  obtain ⟨h₈, h₉, h₁₀⟩ :=
    Random.MEq_ExpectCond.MEq_ExpectCond.MEq_ExpectCond.of.MEqExpectS.All_MEq_ExpectCondDot.All_MEq_ExpectCondDot.GtInftySup.In_Ico
      h₀ h₁ h₂ h₄ h₅ae h₆
  have hQi : Integrable (fun ω ↦ Q t (s t ω) (a t ω)) π := integrable_condExp.congr (h₄ t).symm
  have hri : Integrable (r t) π :=
    Integrable.of_bound (hrm t).aestronglyMeasurable |R|
      (Filter.Eventually.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le ((hbd t ω).trans (le_abs_self R)))
  have hVi : Integrable (fun ω ↦ V (t + 1) (s (t + 1) ω)) π := integrable_condExp.congr (h₅ae (t + 1)).symm
  have hF : Integrable (fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) π := hri.add (hVi.const_mul γ)
  have hmap_of : π (s t ⁻¹' {x}) ≠ 0 → π.map (s t) {x} ≠ 0 := by
    intro hpos
    rwa [Measure.map_apply (hsm t) (measurableSet_singleton x)]
  refine ⟨?_, ?_, h₁₀⟩
  · intro hpos
    simp only [Expectation.asRV_process]
    rw [Expectation.condEval_eq_integral hpa (hsm t)
      (show Measurable fun integ : ℕ → A ↦ Q t x (integ t) from (h₃ t x).comp (measurable_pi_apply t))
      (hmap_of hpos)]
    rw [Random.Eq.of.Ne_0.MEq (u := V t) (v := fun y ↦ ∫ ω, Q t (s t ω) (a t ω) ∂π[|s t ⁻¹' {y}])
      (h₈.trans (Random.MEqCondExp_Integral.of.Integrable.Measurable (hsm t) hQi)) hpos]
    exact integral_congr_ae ((ae_cond_mem (hsm t (measurableSet_singleton x))).mono fun ω hω ↦ by
      dsimp only
      rw [show s t ω = x from hω])
  · intro hpos
    simp only [Expectation.asRV_process]
    rw [Expectation.condEval_eq_integral hpr (hsm t) hf (hmap_of hpos)]
    exact Random.Eq.of.Ne_0.MEq (u := V t)
      (v := fun y ↦ ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂π[|s t ⁻¹' {y}])
      (h₉.trans (Random.MEqCondExp_Integral.of.Integrable.Measurable (hsm t) hF)) hpos


-- created on 2026-10-06
-- updated on 2026-11-12
