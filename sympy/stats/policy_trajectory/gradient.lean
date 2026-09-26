import sympy.stats.policy_trajectory.markov
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Differentiability API for the policy-gradient trajectory model

Facts about `PolicyGradient.Model` used by the policy-gradient lemmas
(`Tensor.EqGrad.*.policy_gradient.*`, `Tensor.Eq.Grad.Expect.*.policy_gradient`, …), under the
hypotheses that every `θ ↦ π_θ(u | x)` is differentiable with a globally bounded gradient:

* `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` and `P1 θ x y = Pr(s[t+1] = y | s[t] = x)`, the
  Chapman–Kolmogorov identity `Pn_succ'`, and `Pr(s[t] = y) = ∑ x, Pr(s[0] = x) * Pn θ t x y`;
* differentiability and gradient bounds of the kernel expectations `W` (`W_diff`);
* the time-free closed forms `Vc`, `Qc` of the value functions, their differentiability and the
  gradient of the Bellman equation (`grad_Vc`);
* local agreement of `M.V` with `Vc` on reachable states, and the finite-sum form of expectations
  of functions of `(s[t], a[t])`.

No `Lemma.*` module is imported here.
-/
open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` (time-homogeneous `n`-step state transition) -/
noncomputable def Pn (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : ℝ :=
  M.W θ (fun z => if z.1 = y then (1:ℝ) else 0) n x

/-- `P1 θ x y = Pr(s[t+1] = y | s[t] = x) = ∑ u, π_θ(u | x) * T(x, u, y)` -/
noncomputable def P1 (M : Model Θ S A) (θ : Θ) (x y : S) : ℝ :=
  ∑ u, M.pol.prob θ x u * M.T x u y

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq A] in
theorem ind_fst_bdd (y : S) (z : Step S A) : ‖(if z.1 = y then (1:ℝ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

omit [DecidableEq A] in
theorem Pn_zero (M : Model Θ S A) (θ : Θ) (x y : S) :
    M.Pn θ 0 x y = if x = y then 1 else 0 :=
  W_fst_zero M θ (fun x' => if x' = y then (1:ℝ) else 0) x

omit [DecidableEq A] in
theorem Pn_succ (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) :
    M.Pn θ (n + 1) x y = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ n y' y :=
  W_succ M θ (ind_fst_sm y) (ind_fst_bdd y) n x

omit [DecidableEq A] in
theorem Pn_one (M : Model Θ S A) (θ : Θ) (x y : S) : M.Pn θ 1 x y = M.P1 θ x y := by
  rw [Pn_succ]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [Pn_zero]

omit [DecidableEq A] in
/-- Chapman–Kolmogorov: `Pr(s[n+1] = z | s[0] = x) = ∑ y, Pr(s[n] = y | s[0] = x) * Pr(s[1] = z | s[0] = y)` -/
theorem Pn_succ' (M : Model Θ S A) (θ : Θ) (n : ℕ) (x z : S) :
    M.Pn θ (n + 1) x z = ∑ y, M.Pn θ n x y * M.P1 θ y z := by
  induction n generalizing x with
  | zero =>
    rw [Pn_one]
    simp [Pn_zero]
  | succ n ih =>
    calc M.Pn θ (n + 1 + 1) x z
        = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ (n + 1) y' z := Pn_succ M θ (n + 1) x z
      _ = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * ∑ y, M.Pn θ n y' y * M.P1 θ y z := by
          simp_rw [ih]
      _ = ∑ y, (∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ n y' y) * M.P1 θ y z := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ y, M.Pn θ (n + 1) x y * M.P1 θ y z := by
          simp_rw [Pn_succ]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem T_sum (M : Model Θ S A) (x : S) (u : A) : ∑ y, M.T x u y = 1 := by
  have := M.env.trans_markov
  unfold Model.T
  rw [sum_measureReal_singleton]
  simp

omit [DecidableEq A] in
theorem E_s_f (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (t j : ℕ) (x : S) :
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f (ω (t + j)) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.W θ f j x := by
  have hK := Kf_bdd M θ hf hC j
  exact (stage_iter M θ hf hC t j (ind_fst_sm x) (ind_bdd _)).trans (stage_split M θ t hK.1 hK.2 x)

omit [MeasurableSingletonClass A] [DecidableEq A] in
theorem real_inter (M : Model Θ S A) (θ : Θ) (t t' : ℕ) (x y : S) :
    (M.traj θ).real (s t ⁻¹' {x} ∩ s t' ⁻¹' {y}) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s t' ω = y then (1:ℝ) else 0) ∂(M.traj θ) := by
  rw [← integral_indicator_one ((s_meas t (measurableSet_singleton x)).inter
    (s_meas t' (measurableSet_singleton y)))]
  congr 1
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : s t' ω = y <;> simp [Set.indicator, h1, h2]

omit [DecidableEq A] in
theorem cond_Pn (M : Model Θ S A) (θ : Θ) (t n : ℕ) (x y : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    ((M.traj θ)[|s t ⁻¹' {x}]).real (s (t + n) ⁻¹' {y}) = M.Pn θ n x y := by
  rw [measureReal_def, cond_apply (s_meas t (measurableSet_singleton x)), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, real_inter,
    show (∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + n) ω = y then (1:ℝ) else 0) ∂(M.traj θ)) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.Pn θ n x y from E_s_f M θ (ind_fst_sm y) (ind_fst_bdd y) t n x,
    inv_mul_cancel_left₀ hP]

omit [DecidableEq A] in
theorem cond_P1 (M : Model Θ S A) (θ : Θ) (t : ℕ) (x y : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    ((M.traj θ)[|s t ⁻¹' {x}]).real (s (t + 1) ⁻¹' {y}) = M.P1 θ x y := by
  rw [cond_Pn M θ t 1 x y hP, Pn_one]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem P_zero (M : Model Θ S A) (θ : Θ) (x : S) :
    (M.traj θ).real (s 0 ⁻¹' {x}) = M.env.init.real {x} := by
  have h : (M.traj θ).map (s 0) = ((M.traj θ).map (fun ω => ω 0)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]; rfl
  rw [measureReal_def, ← Measure.map_apply (s_meas 0) (measurableSet_singleton x), h, stage_zero,
    Model.μ₀, fst_stageK_comp, measureReal_def]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem ind_sum (x₀ : S) : ∑ x, (if x₀ = x then (1:ℝ) else 0) = 1 := by
  simp

omit [DecidableEq A] in
theorem P_eq (M : Model Θ S A) (θ : Θ) (t : ℕ) (y : S) :
    (M.traj θ).real (s t ⁻¹' {y}) = ∑ x, M.env.init.real {x} * M.Pn θ t x y := by
  rw [← integral_indicator_one (s_meas t (measurableSet_singleton y))]
  have h₁ : ∀ ω, (s t ⁻¹' {y}).indicator (1 : (ℕ → Step S A) → ℝ) ω =
      ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * (if (ω (0 + t)).1 = y then (1:ℝ) else 0) := by
    intro ω
    rw [← Finset.sum_mul, ind_sum, one_mul, zero_add]
    by_cases h : s t ω = y <;> simp [Set.indicator, h] <;> exact h
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => by
    exact integrable_ind_h M θ (fun ω => (s 0 ω, s (0 + t) ω))
      ((s_meas 0).prodMk (s_meas (0 + t))) (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [E_s_f M θ (ind_fst_sm y) (ind_fst_bdd y) 0 t x, P_zero]
  rfl

omit [DecidableEq A] in
theorem E_r (M : Model Θ S A) (θ : Θ) (t : ℕ) :
    ∫ ω, r t ω ∂(M.traj θ) = ∑ x, M.env.init.real {x} * M.W θ M.rc t x := by
  have h₁ : ∀ ω : ℕ → Step S A, r t ω = ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * r (0 + t) ω := by
    intro ω
    rw [← Finset.sum_mul, ind_sum, one_mul, zero_add]
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => integrable_ind_r M θ (s 0) (s_meas 0)
    (fun y => if y = x then (1:ℝ) else 0) (0 + t))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [E_s_r M θ 0 t x, P_zero]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem W_bnd (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) (y : S) : ‖M.W θ f j y‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall (Kf_bdd M θ hf hC j).2)
  show ‖∫ z, M.Kf θ f j z ∂(M.stageK θ y)‖ ≤ _
  simpa using h

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem reward_int_bdd (M : Model Θ S A) {f : Step S A → ℝ} {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    (y : S) (u : A) : ‖∫ ρ, f (y, u, ρ) ∂(M.env.reward (y, u))‖ ≤ C := by
  have := M.env.reward_markov
  have h := norm_integral_le_of_norm_le_const (μ := M.env.reward (y, u))
    (Filter.Eventually.of_forall fun ρ => hC (y, u, ρ))
  simpa using h

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem init_sum (M : Model Θ S A) : ∑ x, M.env.init.real {x} = 1 := by
  have := M.env.init_prob
  rw [sum_measureReal_singleton]
  simp

/-- time-free closed form of the state-value function: `Vc θ γ x = ∑' k, γ ^ k * 𝔼[r[t+k] | s[t] = x]` -/
noncomputable def Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.W θ M.rc k x

/-- time-free closed form of the action-value function:
`Qc θ γ x u = 𝔼[r | x, u] + γ * ∑ y, T(x, u, y) * Vc θ γ y` -/
noncomputable def Qc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  (∫ ρ, M.rc (x, u, ρ) ∂(M.env.reward (x, u))) + γ * ∑ y, M.T x u y * M.Vc θ γ y

omit [DecidableEq S] [DecidableEq A] in
theorem Vc_bellman (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (x : S) :
    M.Vc θ γ x = ∑ u, M.pol.prob θ x u * M.Qc θ γ x u := by
  unfold Model.Qc Model.Vc
  rw [v_closed M θ hγ x, W_zero M θ (rc_sm M) (rc_bdd M) x, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

omit [DecidableEq A] in
theorem V_eq_Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (t : ℕ) (x : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) : M.V θ γ t x = M.Vc θ γ x :=
  V_eq M θ γ t x hP

theorem Q_eq_Qc (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S) (u : A)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u ≠ 0) : M.Q θ γ t x u = M.Qc θ γ x u :=
  Q_eq M θ hγ t x u hP

section grad

variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

omit [DecidableEq S] [DecidableEq A] in
theorem W_diff (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp)
    {f : Step S A → ℝ} (hf : StronglyMeasurable f) {Cf : ℝ} (hCf : ∀ z, ‖f z‖ ≤ Cf) (j : ℕ) (y : S) :
    Differentiable ℝ (fun θ => M.W θ f j y) ∧
      ∀ θ, ‖fderiv ℝ (fun θ => M.W θ f j y) θ‖ ≤ (j + 1) * (Fintype.card A * Cp * Cf) := by
  induction j generalizing y with
  | zero =>
    have e : (fun θ => M.W θ f 0 y) =
        fun θ => ∑ u, M.pol.prob θ y u * ∫ ρ, f (y, u, ρ) ∂(M.env.reward (y, u)) :=
      funext fun θ => W_zero M θ hf hCf y
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((hd y u) θ).mul_const _, fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((hd y u) θ).mul_const _]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ y u * ∫ ρ, f (y, u, ρ) ∂(M.env.reward (y, u))) θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _u : A, Cf * Cp := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_mul_const ((hd y u) θ), norm_smul]
          exact mul_le_mul (reward_int_bdd M hCf y u) (hC θ y u) (norm_nonneg _)
            ((norm_nonneg _).trans (hCf (y, u, 0)))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; push_cast; ring
  | succ j ih =>
    have e : (fun θ => M.W θ f (j + 1) y) =
        fun θ => ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.W θ f j y' :=
      funext fun θ => W_succ M θ hf hCf j y
    have hg : ∀ u, Differentiable ℝ (fun θ => ∑ y', M.T y u y' * M.W θ f j y') :=
      fun u θ => DifferentiableAt.fun_sum fun y' _ => ((ih y').1 θ).const_mul _
    have hg' : ∀ u θ, ‖fderiv ℝ (fun θ => ∑ y', M.T y u y' * M.W θ f j y') θ‖ ≤
        (j + 1) * (Fintype.card A * Cp * Cf) := by
      intro u θ
      rw [fderiv_fun_sum fun y' _ => ((ih y').1 θ).const_mul _]
      calc _ ≤ ∑ y', ‖fderiv ℝ (fun θ => M.T y u y' * M.W θ f j y') θ‖ := norm_sum_le _ _
        _ ≤ ∑ y', M.T y u y' * ((j + 1) * (Fintype.card A * Cp * Cf)) := by
            refine Finset.sum_le_sum fun y' _ => ?_
            rw [fderiv_const_mul ((ih y').1 θ), norm_smul, Real.norm_of_nonneg (T_nonneg M y u y')]
            exact mul_le_mul_of_nonneg_left ((ih y').2 θ) (T_nonneg M y u y')
        _ = _ := by rw [← Finset.sum_mul, T_sum, one_mul]
    have hgb : ∀ u θ, ‖∑ y', M.T y u y' * M.W θ f j y'‖ ≤ Cf := by
      intro u θ
      calc _ ≤ ∑ y', ‖M.T y u y' * M.W θ f j y'‖ := norm_sum_le _ _
        _ ≤ ∑ y', M.T y u y' * Cf := by
            refine Finset.sum_le_sum fun y' _ => ?_
            rw [norm_mul, Real.norm_of_nonneg (T_nonneg M y u y')]
            exact mul_le_mul_of_nonneg_left (W_bnd M θ hf hCf j y') (T_nonneg M y u y')
        _ = Cf := by rw [← Finset.sum_mul, T_sum, one_mul]
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((hd y u) θ).fun_mul ((hg u) θ), fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((hd y u) θ).fun_mul ((hg u) θ)]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ y u * ∑ y', M.T y u y' * M.W θ f j y') θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ u, (M.pol.prob θ y u * ((j + 1) * (Fintype.card A * Cp * Cf)) + Cf * Cp) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_fun_mul ((hd y u) θ) ((hg u) θ)]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg (M.pol.nonneg θ y u)]
            exact mul_le_mul_of_nonneg_left (hg' u θ) (M.pol.nonneg θ y u)
          · rw [norm_smul]
            exact mul_le_mul (hgb u θ) (hC θ y u) (norm_nonneg _) ((norm_nonneg _).trans (hCf (y, u, 0)))
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.pol.sum_eq_one, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          push_cast; ring

omit [DecidableEq A] in
theorem P_diff (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) (t : ℕ) (y : S) :
    Differentiable ℝ (fun θ => (M.traj θ).real (s t ⁻¹' {y})) := by
  have e : (fun θ => (M.traj θ).real (s t ⁻¹' {y})) = fun θ => ∑ x, M.env.init.real {x} * M.Pn θ t x y :=
    funext fun θ => P_eq M θ t y
  rw [e]
  exact fun θ => DifferentiableAt.fun_sum fun x _ =>
    ((W_diff M hd hC (ind_fst_sm y) (ind_fst_bdd y) t x).1 θ).const_mul _

omit [DecidableEq A] in
theorem V_nhds (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) (γ : ℝ) (t : ℕ) (x : S) (θ : Θ)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    (fun θ' => M.V θ' γ t x) =ᶠ[𝓝 θ] fun θ' => M.Vc θ' γ x := by
  have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {x})) θ :=
    (P_diff M hd hC t x θ).continuousAt
  filter_upwards [hc.eventually_ne hP] with θ' h
  exact V_eq_Vc M θ' γ t x h

theorem summable_lin {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (K : ℝ) :
    Summable (fun k : ℕ => γ ^ k * ((k + 1) * K)) := by
  have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * γ ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hγ.1]; exact hγ.2)
  have h2 := summable_geometric_of_lt_one hγ.1 hγ.2
  exact ((h1.add h2).mul_right K).congr fun k => by ring

omit [DecidableEq S] [DecidableEq A] in
theorem Vc_hasFDerivAt (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (x : S) (θ : Θ) :
    HasFDerivAt (fun θ => M.Vc θ γ x) (∑' k, γ ^ k • fderiv ℝ (fun θ => M.W θ M.rc k x) θ) θ := by
  have hW := fun k => W_diff M hd hC (rc_sm M) (rc_bdd M) k x
  exact hasFDerivAt_tsum (summable_lin hγ (Fintype.card A * Cp * |M.env.R|))
    (fun k θ => ((hW k).1 θ).hasFDerivAt.const_mul (γ ^ k))
    (fun k θ => by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg hγ.1]
      exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg hγ.1 k))
    (summable_W M θ hγ x) θ

omit [DecidableEq S] [DecidableEq A] in
theorem Vc_diff (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (x : S) : Differentiable ℝ (fun θ => M.Vc θ γ x) :=
  fun θ => (Vc_hasFDerivAt M hd hC hγ x θ).differentiableAt

omit [DecidableEq S] [DecidableEq A] in
theorem grad_Qc (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (x : S) (u : A) (θ : Θ) :
    DifferentiableAt ℝ (fun θ => M.Qc θ γ x u) θ ∧
      fderiv ℝ (fun θ => M.Qc θ γ x u) θ = γ • ∑ y, M.T x u y • fderiv ℝ (fun θ => M.Vc θ γ y) θ := by
  have hs : DifferentiableAt ℝ (fun θ => ∑ y, M.T x u y * M.Vc θ γ y) θ :=
    DifferentiableAt.fun_sum fun y _ => ((Vc_diff M hd hC hγ y) θ).const_mul _
  refine ⟨(hs.const_mul γ).const_add _, ?_⟩
  unfold Model.Qc
  rw [fderiv_const_add, fderiv_const_mul hs,
    fderiv_fun_sum fun y _ => ((Vc_diff M hd hC hγ y) θ).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun y _ => fderiv_const_mul ((Vc_diff M hd hC hγ y) θ) _

omit [DecidableEq S] [DecidableEq A] in
/-- gradient of the Bellman equation for the closed-form value function -/
theorem grad_Vc (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (x : S) (θ : Θ) :
    fderiv ℝ (fun θ => M.Vc θ γ x) θ =
      ∑ u, M.Qc θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ +
        γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ => M.Vc θ γ y) θ := by
  have hb : (fun θ => M.Vc θ γ x) = fun θ => ∑ u, M.pol.prob θ x u * M.Qc θ γ x u :=
    funext fun θ => Vc_bellman M θ hγ x
  have hQ := fun u => grad_Qc M hd hC hγ x u θ
  rw [hb, fderiv_fun_sum fun u _ => ((hd x u) θ).fun_mul (hQ u).1]
  simp_rw [fderiv_fun_mul ((hd _ _) θ) (hQ _).1, (hQ _).2]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  unfold Model.P1
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
  congr 1
  ring

omit [DecidableEq A] in
theorem grad_V_eq (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) (γ : ℝ) (t : ℕ) (x : S) (θ : Θ)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    fderiv ℝ (fun θ' => M.V θ' γ t x) θ = fderiv ℝ (fun θ' => M.Vc θ' γ x) θ :=
  (V_nhds M hd hC γ t x θ hP).fderiv_eq

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem dpi_zero (M : Model Θ S A) (θ : Θ) (x : S) (u : A) (h : M.pol.prob θ x u = 0) :
    fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ = 0 := by
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun θ' => ?_)
  show M.pol.prob θ x u ≤ M.pol.prob θ' x u
  rw [h]
  exact M.pol.nonneg θ' x u

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem pi_gradlog (M : Model Θ S A)
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u)) (θ : Θ) (x : S) (u : A) :
    M.pol.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ =
      fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ := by
  by_cases h : M.pol.prob θ x u = 0
  · rw [h, zero_smul, dpi_zero M θ x u h]
  · rw [fderiv.log ((hd x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
/-- zero expected score: `∑ u, π_θ(u | x) • ∇ log π_θ(u | x) = 0` (no positivity needed) -/
theorem score_zero (M : Model Θ S A)
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u)) (θ : Θ) (x : S) :
    ∑ u, M.pol.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ = 0 := by
  simp_rw [pi_gradlog M hd θ x]
  rw [← fderiv_fun_sum fun u _ => (hd x u) θ]
  simp_rw [M.pol.sum_eq_one]
  exact fderiv_const_apply 1

/-- policy-gradient recursion for the model value functions on a reachable state -/
theorem grad_V_rec (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (t : ℕ) (x : S) (θ : Θ) (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    fderiv ℝ (fun θ' => M.V θ' γ t x) θ =
      ∑ u, M.Q θ γ t x u • fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ +
        γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ := by
  rw [grad_V_eq M hd hC γ t x θ hP, grad_Vc M hd hC hγ x θ]
  congr 1
  · refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : M.pol.prob θ x u = 0
    · rw [dpi_zero M θ x u hu, smul_zero, smul_zero]
    · rw [Q_eq_Qc M θ hγ t x u (mul_ne_zero hP hu)]
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : M.P1 θ x y = 0
    · rw [hy, zero_smul, zero_smul]
    · obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      rw [grad_V_eq M hd hC γ (t + 1) y θ (reach M θ t x u y hP hu)]

end grad

theorem E_sa (M : Model Θ S A) (θ : Θ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (t : ℕ) (φ : S → A → E) :
    ∫ ω, φ (s t ω) (a t ω) ∂(M.traj θ) =
      ∑ y, ∑ u, ((M.traj θ).real (s t ⁻¹' {y}) * M.pol.prob θ y u) • φ y u := by
  have hX : Measurable (fun ω : ℕ → Step S A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  have e := integral_map (μ := M.traj θ) hX.aemeasurable
    (f := fun p : S × A => φ p.1 p.2) StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
  rw [map_measureReal_apply hX (measurableSet_singleton _), ← real_sa]
  congr 2
  ext ω
  simp [Prod.ext_iff]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem E_s1 (M : Model Θ S A) (θ : Θ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (t : ℕ) (φ : S → E) :
    ∫ ω, φ (s t ω) ∂(M.traj θ) = ∑ y, (M.traj θ).real (s t ⁻¹' {y}) • φ y := by
  have e := integral_map (μ := M.traj θ) (s_meas t).aemeasurable
    (f := φ) StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_measureReal_apply (s_meas t) (measurableSet_singleton _)]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem Q_bdd (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S) (u : A) :
    ‖M.Q θ γ t x u‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
  unfold Model.Q
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (cond_r_bdd M θ _ (t + k)) (pow_nonneg hγ.1 k)

omit [DecidableEq A] in
theorem Er_bdd (M : Model Θ S A) (θ : Θ) (t : ℕ) : ‖∫ ω, r t ω ∂(M.traj θ)‖ ≤ |M.env.R| := by
  rw [E_r]
  calc _ ≤ ∑ x, ‖M.env.init.real {x} * M.W θ M.rc t x‖ := norm_sum_le _ _
    _ ≤ ∑ x, M.env.init.real {x} * |M.env.R| := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul, Real.norm_of_nonneg measureReal_nonneg]
        exact mul_le_mul_of_nonneg_left (W_bdd M θ t x) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, init_sum, one_mul]

omit [DecidableEq A] in
theorem obj_eq (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) :
    ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ) = ∑ x, M.env.init.real {x} * M.Vc θ γ x := by
  simp_rw [E_r M θ]
  exact tsum_pull _ _ (fun x => summable_W M θ hγ x)

theorem E_ind_r (M : Model Θ S A) (θ : Θ) (t k : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω ∂(M.traj θ) =
      ((M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) *
        ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
  by_cases h : (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u = 0
  · rw [h, zero_mul]
    cases k with
    | zero => rw [add_zero, E_xu_r0, h, zero_mul]
    | succ j => rw [E_xu_r, h, zero_mul]
  · rw [cond_sa, mul_inv_cancel_left₀ h]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem r_bdd_ae (M : Model Θ S A) (θ : Θ) :
    ∀ᵐ ω ∂(M.traj θ), ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
  rw [ae_all_iff]
  exact fun k => (r_ae M θ k).mono fun ω h => by rw [h]; exact rc_bdd M _

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] in
theorem r_meas (k : ℕ) : Measurable (r (S := S) (A := A) k) :=
  measurable_snd.snd.comp (measurable_pi_apply k)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem G_hasSum (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) :
    ∀ᵐ ω ∂(M.traj θ), HasSum (fun k => γ ^ k * r (t + k) ω) (G γ t ω) ∧
      ‖G γ t ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
  filter_upwards [r_bdd_ae M θ] with ω h
  have hb : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
    exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k)
  have hs : Summable (fun k => γ ^ k * r (t + k) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right _) hb
  exact ⟨hs.hasSum, tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right _) hb⟩

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem G_int (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) :
    Integrable (G γ t) (M.traj θ) := by
  have hm : AEStronglyMeasurable (G γ t) (M.traj θ) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ k ∈ Finset.range n, γ ^ k * r (t + k) ω) (fun n => ?_) ?_
    · exact (Finset.measurable_fun_sum _ fun k _ =>
        (r_meas (t + k)).const_mul (γ ^ k)).aestronglyMeasurable
    · exact (G_hasSum M θ hγ t).mono fun ω h => h.1.tendsto_sum_nat
  exact Integrable.of_bound hm _ ((G_hasSum M θ hγ t).mono fun ω h => h.2)

theorem E_ind_G (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G γ t ω ∂(M.traj θ) =
      ((M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) * M.Q θ γ t x u := by
  have hX : Measurable (fun ω : ℕ → Step S A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  let φ : S × A → ℝ := fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0
  have hF : ∀ k, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)) (M.traj θ) := fun k =>
    ((integrable_ind_r M θ _ hX φ (t + k)).const_mul (γ ^ k)).congr
      (ae_of_all _ fun ω => by simp only [φ]; ring)
  have hN : ∀ k, ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)‖
      ∂(M.traj θ) ≤ γ ^ k * |M.env.R| := by
    intro k
    have hb : ∀ᵐ ω ∂(M.traj θ), ‖‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (γ ^ k * r (t + k) ω)‖‖ ≤ γ ^ k * |M.env.R| := by
      filter_upwards [r_bdd_ae M θ] with ω h
      rw [norm_norm, norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
      exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg hγ.1 k) (norm_nonneg _))
        (by split_ifs <;> simp)).trans (mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k))
    have := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at this
    exact (Real.le_norm_self _).trans this
  have hS : Summable (fun k => ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)‖ ∂(M.traj θ)) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) hN
      ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right _)
  have e : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G γ t ω =
      ∑' k, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) := fun ω => by
    rw [tsum_mul_left]; rfl
  simp_rw [e]
  rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
  have e2 : ∀ k, ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) ∂(M.traj θ) =
      ((M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) *
        (γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]) := fun k => by
    rw [show (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)) =
      fun ω => γ ^ k * ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω) from
        funext fun ω => by ring, integral_const_mul, E_ind_r]
    ring
  simp_rw [e2]
  rw [tsum_mul_left]
  rfl

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem ind_smul_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ)
    (ω : ℕ → Step S A) (c : ℝ) (ψ : S → A → E) :
    c • ψ (s t ω) (a t ω) =
      ∑ x, ∑ u, ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * c) • ψ x u := by
  rw [Finset.sum_eq_single (s t ω) (fun b _ hb => Finset.sum_eq_zero fun u _ => by simp [Ne.symm hb])
    (by simp)]
  rw [Finset.sum_eq_single (a t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- `𝔼[G[t] • ψ(s[t], a[t])] = 𝔼[Q(s[t], a[t]) • ψ(s[t], a[t])]` -/
theorem E_G_smul (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (t : ℕ) (ψ : S → A → E) :
    ∫ ω, G γ t ω • ψ (s t ω) (a t ω) ∂(M.traj θ) =
      ∫ ω, M.Q θ γ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M.traj θ) := by
  have hX : Measurable (fun ω : ℕ → Step S A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  have hI : ∀ x u, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G γ t ω)
      (M.traj θ) := by
    intro x u
    refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R|) ?_ ?_
    · exact (((disc_sm (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
        hX).aestronglyMeasurable).mul (G_int M θ hγ t).1
    · filter_upwards [G_hasSum M θ hγ t] with ω h
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp) |>.trans h.2
  rw [E_sa M θ t (fun y u => M.Q θ γ t y u • ψ y u)]
  simp_rw [ind_smul_sum t _ (G γ t _) ψ]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_smul_const, E_ind_G M θ hγ t, smul_smul]

section grad2

variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- `𝔼[g(s[t], a[t]) • ∇ log π(a[t] | s[t])] = ∑ y, Pr(s[t] = y) • ∑ u, g y u • ∇ π(u | y)` -/
theorem E_score (M : Model Θ S A)
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u)) (θ : Θ) (t : ℕ) (g : S → A → ℝ) :
    ∫ ω, g (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ
        ∂(M.traj θ) =
      ∑ y, (M.traj θ).real (s t ⁻¹' {y}) •
        ∑ u, g y u • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ := by
  rw [E_sa M θ t (fun y u => g y u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← pi_gradlog M hd θ y u, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- `𝔼[h(s[t]) • ∇ log π(a[t] | s[t])] = 0` -/
theorem E_h_score (M : Model Θ S A)
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u)) (θ : Θ) (t : ℕ) (h : S → ℝ) :
    ∫ ω, h (s t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ
        ∂(M.traj θ) = 0 := by
  rw [E_sa M θ t (fun y u => h y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  refine Finset.sum_eq_zero fun y _ => ?_
  have h₁ : ∀ u, ((M.traj θ).real (s t ⁻¹' {y}) * M.pol.prob θ y u) •
      (h y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ) =
      ((M.traj θ).real (s t ⁻¹' {y}) * h y) •
        (M.pol.prob θ y u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ) := fun u => by
    rw [smul_smul, smul_smul]; congr 1; ring
  simp_rw [h₁]
  rw [← Finset.smul_sum, score_zero M hd θ y, smul_zero]

omit [DecidableEq A] in
theorem Er_diff (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) (t : ℕ) :
    Differentiable ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) ∧
      ∀ θ, ‖fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ‖ ≤
        (t + 1) * (Fintype.card A * Cp * |M.env.R|) := by
  have e : (fun θ => ∫ ω, r t ω ∂(M.traj θ)) = fun θ => ∑ x, M.env.init.real {x} * M.W θ M.rc t x :=
    funext fun θ => E_r M θ t
  rw [e]
  have hW := fun x => W_diff M hd hC (rc_sm M) (rc_bdd M) t x
  refine ⟨fun θ => DifferentiableAt.fun_sum fun x _ => ((hW x).1 θ).const_mul _, fun θ => ?_⟩
  rw [fderiv_fun_sum fun x _ => ((hW x).1 θ).const_mul _]
  calc _ ≤ ∑ x, ‖fderiv ℝ (fun θ => M.env.init.real {x} * M.W θ M.rc t x) θ‖ := norm_sum_le _ _
    _ ≤ ∑ x, M.env.init.real {x} * ((t + 1) * (Fintype.card A * Cp * |M.env.R|)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [fderiv_const_mul ((hW x).1 θ), norm_smul, Real.norm_of_nonneg measureReal_nonneg]
        exact mul_le_mul_of_nonneg_left ((hW x).2 θ) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, init_sum, one_mul]

omit [DecidableEq A] in
/-- `∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑' t, γ ^ t • ∇ 𝔼[r[t]]` -/
theorem obj_hasFDerivAt (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (θ : Θ) :
    HasFDerivAt (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ))
      (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ) θ := by
  refine hasFDerivAt_tsum (x₀ := θ) (summable_lin hγ (Fintype.card A * Cp * |M.env.R|))
    (fun t θ => ((Er_diff M hd hC t).1 θ).hasFDerivAt.const_mul (γ ^ t))
    (fun t θ => ?_) ?_ θ
  · rw [norm_smul, norm_pow, Real.norm_of_nonneg hγ.1]
    exact mul_le_mul_of_nonneg_left ((Er_diff M hd hC t).2 θ) (pow_nonneg hγ.1 t)
  · refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|)
      fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
    exact mul_le_mul_of_nonneg_left (Er_bdd M θ t) (pow_nonneg hγ.1 t)

omit [DecidableEq A] in
/-- `∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑ x, Pr(s[0] = x) • ∇ Vc(x)` -/
theorem grad_obj (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (θ : Θ) :
    ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
      ∑ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ := by
  rw [← (obj_hasFDerivAt M hd hC hγ θ).fderiv]
  have e : (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ)) =
      fun θ => ∑ x, M.env.init.real {x} * M.Vc θ γ x := funext fun θ => obj_eq M θ hγ
  rw [e, fderiv_fun_sum fun x _ => ((Vc_diff M hd hC hγ x) θ).const_mul _]
  exact Finset.sum_congr rfl fun x _ => fderiv_const_mul ((Vc_diff M hd hC hγ x) θ) _

end grad2

omit [DecidableEq A] in
theorem Pn_nonneg (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : 0 ≤ M.Pn θ n x y := by
  induction n generalizing x with
  | zero => rw [Pn_zero]; split_ifs <;> norm_num
  | succ n ih =>
    rw [Pn_succ]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (M.pol.nonneg θ x u)
      (Finset.sum_nonneg fun y' _ => mul_nonneg (T_nonneg M x u y') (ih y'))

omit [DecidableEq A] in
theorem reach_n (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S)
    (h₀ : (M.traj θ).real (s 0 ⁻¹' {x}) ≠ 0) (h : M.Pn θ n x y ≠ 0) :
    (M.traj θ).real (s n ⁻¹' {y}) ≠ 0 := by
  rw [P_eq]
  rw [P_zero] at h₀
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun x' => M.env.init.real {x'} * M.Pn θ n x' y)
    (fun x' _ => mul_nonneg measureReal_nonneg (Pn_nonneg M θ n x' y)) (Finset.mem_univ x)))
  exact mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm h₀))
    (lt_of_le_of_ne (Pn_nonneg M θ n x y) (Ne.symm h))

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem P_sum (M : Model Θ S A) (θ : Θ) (t : ℕ) : ∑ y, (M.traj θ).real (s t ⁻¹' {y}) = 1 := by
  have h := E_s1 M θ t (fun _ => (1:ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h.symm

omit [DecidableEq S] [DecidableEq A] in
theorem integrable_sa (M : Model Θ S A) (θ : Θ) {E : Type*} [NormedAddCommGroup E] (t : ℕ)
    (φ : S → A → E) : Integrable (fun ω => φ (s t ω) (a t ω)) (M.traj θ) := by
  have hX : Measurable (fun ω : ℕ → Step S A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  refine Integrable.of_bound (C := ∑ p : S × A, ‖φ p.1 p.2‖)
    ((StronglyMeasurable.of_discrete (f := fun p : S × A => φ p.1 p.2)).comp_measurable
      hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun p : S × A => ‖φ p.1 p.2‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (s t ω, a t ω))

omit [DecidableEq S] [DecidableEq A] in
theorem integrable_G_smul (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ) (ψ : S → A → E) :
    Integrable (fun ω => G γ t ω • ψ (s t ω) (a t ω)) (M.traj θ) := by
  have hX : Measurable (fun ω : ℕ → Step S A => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R| * ∑ p : S × A, ‖ψ p.1 p.2‖)
    ((G_int M θ hγ t).1.smul ((StronglyMeasurable.of_discrete
      (f := fun p : S × A => ψ p.1 p.2)).comp_measurable hX).aestronglyMeasurable) ?_
  filter_upwards [G_hasSum M θ hγ t] with ω h
  rw [norm_smul]
  exact mul_le_mul h.2 (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
    ((norm_nonneg _).trans h.2)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
/-- almost surely every visited state is reachable -/
theorem reach_ae (M : Model Θ S A) (θ : Θ) :
    ∀ᵐ ω ∂(M.traj θ), ∀ k, (M.traj θ).real (s k ⁻¹' {s k ω}) ≠ 0 := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω : ℕ → Step S A | ¬ (M.traj θ).real (s (A := A) k ⁻¹' {s k ω}) ≠ 0} =
      ⋃ y ∈ {y : S | (M.traj θ).real (s (A := A) k ⁻¹' {y}) = 0}, s (A := A) k ⁻¹' {y} := by
    ext ω; simp
  rw [e]
  exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy => meas_zero_of_real M θ hy

omit [DecidableEq A] in
theorem cond_r_W (M : Model Θ S A) (θ : Θ) (t k : ℕ) (x : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}] = M.W θ M.rc k x := by
  rw [cond_s, E_s_r, inv_mul_cancel_left₀ hP]

section grad3

variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

omit [DecidableEq A] in
/-- on a reachable state, `∑' k, γ ^ k • ∇ 𝔼[r[t+k] | s[t] = x] = ∇ V(s[t] = x)` -/
theorem sum_grad_cond (M : Model Θ S A) {Cp : ℝ}
    (hd : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
    (hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (t : ℕ) (x : S) (θ : Θ) (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    ∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}]) θ =
      fderiv ℝ (fun θ => M.V θ γ t x) θ := by
  have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {x})) θ :=
    (P_diff M hd hC t x θ).continuousAt
  have hk : ∀ k, fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}]) θ =
      fderiv ℝ (fun θ => M.W θ M.rc k x) θ := by
    intro k
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hc.eventually_ne hP] with θ' h
    exact cond_r_W M θ' t k x h
  simp_rw [hk]
  rw [grad_V_eq M hd hC γ t x θ hP, (Vc_hasFDerivAt M hd hC hγ x θ).fderiv]

end grad3

end Model

end PolicyGradient
