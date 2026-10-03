import Lemma.Tensor.EqExpect.of.Eq_Expect.V_Function
import Lemma.Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function
import Lemma.Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function
import sympy.stats.cond_expectation
open MeasureTheory ProbabilityTheory PolicyGradient


/--
`extract_QVA`: for the action values `Q` (sympy `Q_def`, `h₁`) and state values `V` (sympy `V_def`, `h₂`)
of the trajectory model, indexed by the time `t` of the conditioning state,
`V(s[t]) = 𝔼_{a[t]}[Q(s[t], a[t]) | s[t]]`, `V(s[t]) = 𝔼[r[t] + γ * V(s[t+1]) | s[t]]` and
`Q(s[t], a[t]) = 𝔼[r[t] + γ * V(s[t+1]) | s[t], a[t]]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : ℕ → S → A → ℝ}
  {V : ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t x u, Q t x u = 𝔼[r : M.traj θ](∑' k, γ ^ k * r (t + k) | (fun ω ↦ (s t ω, a t ω)) = (x, u)))
  (h₂ : ∀ t x, V t x = 𝔼[r : M.traj θ](∑' k, γ ^ k * r (t + k) | s t = x))
  (x : S)
  (u : A) :
-- imply
  V t x = 𝔼[a : M.traj θ](Q t x (a t) | s t = x) ∧
    V t x = 𝔼[r, s : M.traj θ](r t + γ * V (t + 1) (s (t + 1)) | s t = x) ∧
    Q t x u = 𝔼[r, s : M.traj θ](r t + γ * V (t + 1) (s (t + 1)) | (fun ω ↦ (s t ω, a t ω)) = (x, u)) := by
-- proof
  have hs : ∀ t, Measurable (s (S := S) (A := A) t) := fun t => measurable_fst.comp (measurable_pi_apply t)
  have ha : ∀ t, Measurable (a (S := S) (A := A) t) := fun t => measurable_fst.comp (measurable_snd.comp (measurable_pi_apply t))
  have hr : ∀ t, Measurable (r (S := S) (A := A) t) := Model.r_meas' (S := S) (A := A)
  have hpa : Measurable (fun ω t ↦ a (S := S) (A := A) t ω) := measurable_pi_lambda _ ha
  have hpr : Measurable (fun ω t ↦ r (S := S) (A := A) t ω, fun ω t ↦ s (S := S) (A := A) t ω) :=
    (measurable_pi_lambda _ hr).prodMk (measurable_pi_lambda _ hs)
  have hf : Measurable (fun integ : (ℕ → ℝ) × (ℕ → S) ↦ integ.1 t + γ * ∫ ω, G (S := S) (A := A) γ (t + 1) ω ∂(M.traj θ)[|s (t + 1) ⁻¹' {integ.2 (t + 1)}]) :=
    ((measurable_pi_apply t).comp measurable_fst).add
      (((measurable_of_countable (fun y : S ↦ ∫ ω, G (S := S) (A := A) γ (t + 1) ω ∂(M.traj θ)[|s (t + 1) ⁻¹' {y}])).comp
        ((measurable_pi_apply (t + 1)).comp measurable_snd)).const_mul γ)
  have hpR : Measurable (fun ω t ↦ r (S := S) (A := A) t ω) := measurable_pi_lambda _ hr
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hQ : Q = M.Q θ γ := funext fun t => funext fun x => funext fun u => by
    rw [h₁ t x u]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : (fun ω ↦ (s (S := S) (A := A) t ω, a (S := S) (A := A) t ω)) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
      ext ω; simp [Prod.ext_iff]
    rw [hpre]
    exact Model.integral_G_cond M θ h₀ _ t
  have hV : V = M.V θ γ := funext fun t => funext fun x => by
    rw [h₂ t x, M.V_eq_integral θ γ t x]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  subst hQ hV
  simp only [M.V_eq_integral]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpa.aemeasurable (by fun_prop)]
    exact Tensor.EqExpect.of.Eq_Expect.V_Function h₀ (fun x u => rfl) x
  · simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpr.aemeasurable hf]
    refine (Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function h₀ x).trans ?_
    congr 1
    funext ω
    rw [add_comm]
    rfl
  · simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpr.aemeasurable hf]
    have hpre : (fun ω ↦ (s (S := S) (A := A) t ω, a (S := S) (A := A) t ω)) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
      ext ω; simp [Prod.ext_iff]
    rw [hpre]
    refine (Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function h₀ x u).trans ?_
    congr 1
    funext ω
    rw [add_comm]
    rfl


-- created on 2023-03-28
