import Lemma.Tensor.EqExpect.of.Eq_Expect.V_Function
import Lemma.Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function
import Lemma.Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function
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
  (h₁ : ∀ t x u, Q t x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (h₂ : ∀ t x, V t x = ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₃ : γ ∈ Set.Ico 0 1)
  (x : S)
  (u : A) :
-- imply
  V t x = ∫ ω, Q t x (a t ω) ∂(M.traj θ)[|s t ⁻¹' {x}] ∧
    V t x = ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂(M.traj θ)[|s t ⁻¹' {x}] ∧
    Q t x u = ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
-- proof
  have h₄ : Q = M.Q θ γ := funext fun t => funext fun x => funext fun u => h₁ t x u
  have h₅ : V = M.V θ γ := funext fun t => funext fun x => (h₂ t x).trans (M.V_eq_integral θ γ t x).symm
  subst h₄ h₅
  simp only [M.V_eq_integral]
  refine ⟨Tensor.EqExpect.of.Eq_Expect.V_Function h₃ (fun x u => rfl) x, ?_, ?_⟩
  · refine (Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function h₃ x).trans ?_
    congr 1
    funext ω
    rw [add_comm]
    rfl
  · refine (Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function h₃ x u).trans ?_
    congr 1
    funext ω
    rw [add_comm]
    rfl


-- created on 2023-03-28
