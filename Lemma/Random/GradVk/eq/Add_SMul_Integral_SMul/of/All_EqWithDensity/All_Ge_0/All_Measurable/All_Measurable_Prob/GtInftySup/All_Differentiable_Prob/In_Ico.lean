import sympy.stats.rv
import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import sympy.concrete.summations
import Mathlib.Analysis.InnerProductSpace.Dual
import Lemma.Random.Fderiv.eq.AddSum_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Measurable_Vk.of.All_Measurable_Prob
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
Policy-gradient recursion on a continuous state space (actions stay finite):
∇V(s[t] = s.bvar[t]) = ∑ a.bvar[t], Q(s.bvar[t], a.bvar[t]) • ∇π(a.bvar[t] | s.bvar[t]) + γ • ∫ y, Pr(s[t+1] = y | s[t] = s.bvar[t]) • ∇V(s[t+1] = y) dy,
the gradient of the Bellman equations of extract_QVA; the next-state sum of the discrete version
`Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico`
becomes an integral against the reference measure of `S` (e.g. Lebesgue measure on `ℝ^b`).
Since `Pr(s[t] = x) = 0` for a continuous state, the values `V = Vk`, `Q = Qk` are the regular (kernel) conditional
expectations of the discounted return `γ ** Stack[k](k) @ r[t:]` given `s[t] = x` (resp. `s[t] = x, a[t] = u`),
see `sympy.stats.policy_trajectory.continuous`; `Pr(s[t+1] = y | s[t] = x) = P1k θ p x y = ∑ u, π_θ(u | x) * p x u y`.
h₁, h₂: θ ↦ π_θ(u | x) is differentiable with a bounded gradient (as in the discrete version);
h₃: x ↦ π_θ(u | x) is measurable; h₄, h₅, h₆: `p x u` is a (measurable, nonnegative) density of the transition
`T(· | x, u)` w.r.t. the reference measure. `Θ` is finite-dimensional (the weights `π` have shape `(D,)`).
Differentiation under the integral sign needs no extra hypothesis: ∇V is bounded (from h₂) and `T(· | x, u)` is a
probability measure.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {«s.bvar» : ℕ → S}
  {p : S → A → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₃ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (h₄ : ∀ x u, Measurable (p x u))
  (h₅ : ∀ x u y, p x u y ≥ 0)
  (h₆ : ∀ x u, M.env.trans (x, u) = (ReferenceMeasure.measure : Measure S).withDensity (fun y => ENNReal.ofReal (p x u y))) :
-- imply
  ∇[θ] M.Vk θ γ («s.bvar» t) =
    ∑ «a.bvar» t, M.Qk θ γ («s.bvar» t) («a.bvar» t) • ∇[θ] M.pol.prob θ («s.bvar» t) («a.bvar» t) +
      γ • ∫ y, M.P1k θ p («s.bvar» t) y • ∇[θ] M.Vk θ γ y ∂ReferenceMeasure.measure := by
-- proof
  set x := «s.bvar» t
  have := M.env.trans_markov
  have hF := Fderiv.eq.AddSum_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₀ h₃ x θ
  obtain ⟨C, hC⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₀ h₃
  have hgm : StronglyMeasurable (fun y => fderiv ℝ (fun θ => M.Vk θ γ y) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => Measurable_Vk.of.All_Measurable_Prob (M := M) h₃ θ' γ)
      (fun y => (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₀ h₃ y θ).differentiableAt)
  have hd : ∀ u, ∫ y, fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂(M.env.trans (x, u)) =
      ∫ y, p x u y • fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂ReferenceMeasure.measure := fun u => by
    rw [h₆, integral_withDensity_eq_integral_toReal_smul (h₄ x u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (h₅ x u _)]
  have hi : ∀ u, Integrable (fun y => p x u y • fderiv ℝ (fun θ => M.Vk θ γ y) θ) ReferenceMeasure.measure := fun u => by
    have hI : Integrable (fun y => fderiv ℝ (fun θ => M.Vk θ γ y) θ) (M.env.trans (x, u)) :=
      Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall fun y => by
        have h := hC ⟨(θ, y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
    rw [h₆, integrable_withDensity_iff_integrable_smul' (h₄ x u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)] at hI
    simpa [ENNReal.toReal_ofReal (h₅ x u _)] using hI
  have hsum : ∑ u, M.pol.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂(M.env.trans (x, u)) =
      ∫ y, M.P1k θ p x y • fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂ReferenceMeasure.measure := calc
    _ = ∑ u, ∫ y, M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vk θ γ y) θ) ∂ReferenceMeasure.measure :=
      Finset.sum_congr rfl fun u _ => by rw [hd u, integral_smul]
    _ = ∫ y, ∑ u, M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vk θ γ y) θ) ∂ReferenceMeasure.measure := by
      rw [integral_finsetSum]
      intro u _
      apply Integrable.smul (M.pol.prob θ x u) (hi u)
    _ = _ := by
      congr 1
      funext y
      simp [Model.P1k, Finset.sum_smul, smul_smul]
  have hint : (InnerProductSpace.toDual ℝ Θ).symm (∫ y, M.P1k θ p x y • fderiv ℝ (fun θ => M.Vk θ γ y) θ ∂ReferenceMeasure.measure) =
      ∫ y, (InnerProductSpace.toDual ℝ Θ).symm (M.P1k θ p x y • fderiv ℝ (fun θ => M.Vk θ γ y) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := (ReferenceMeasure.measure : Measure S)) (fun y => M.P1k θ p x y • fderiv ℝ (fun θ => M.Vk θ γ y) θ)
    simpa using h.symm
  simp only [gradient]
  rw [hF, hsum, map_add, map_sum, map_smul, hint]
  simp [map_smul]


-- created on 2026-10-07
