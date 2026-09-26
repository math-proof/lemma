import Lemma.Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Finite-horizon policy gradient: for every `n`,
`γ ** Stack[t](t) @ ∇𝔼[r] = 𝔼[∑ t < n, γ ^ t * Q(s[t], a[t]) • ∇ log π(a[t] | s[t])] + γ ^ n • 𝔼[∇V(s[n])]`,
where `γ ** Stack[t](t) @ ∇𝔼[r]` is `∑' t, γ ^ t • ∇_θ 𝔼[r[t]]`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : ∀ t, IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : ∀ θ t x u, Q θ t x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (h₂ : ∀ θ t x, V θ t x = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₃ : γ ∈ Set.Ico 0 1)
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₅ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖))
  (n : ℕ) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
    ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Q θ t (s t ω) (a t ω)) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) +
      γ ^ n • ∫ ω, fderiv ℝ (fun θ' => V θ' n (s n ω)) θ ∂(M.traj θ) := by
-- proof
  have hQ : Q = fun θ => M.Q θ γ :=
    funext fun θ => funext fun t => funext fun x => funext fun u => h₁ θ t x u
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => h₂ θ t x
  subst hQ hV
  obtain ⟨C, hC⟩ := id h₅
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce
  have h₈ : ∀ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ =
      M.env.init.real {x} • (∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
          ∑ u, M.Q θ γ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
        γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => M.V θ γ n y) θ) := by
    intro x
    by_cases hx : M.env.init.real {x} = 0
    · rw [hx, zero_smul, zero_smul]
    have hP : (M.traj θ).real (s 0 ⁻¹' {x}) ≠ 0 := by rwa [P_zero]
    have h := Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct
      (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) h₀ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      h₃ h₄ h₅ hP n
    have h' : ∀ t y, ((M.traj θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
      have h'' := cond_Pn M θ 0 t x y hP
      rwa [zero_add] at h''
    simp_rw [h'] at h
    rw [← grad_V_eq M h₄ h₇ γ 0 x θ hP, h]
  have h₉ : ∀ t, ∫ ω, (γ ^ t * M.Q θ γ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) =
      ∑ y, (M.traj θ).real (s t ⁻¹' {y}) •
        ∑ u, (γ ^ t * M.Q θ γ t y u) • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ :=
    fun t => E_score M h₄ θ t (fun y u => γ ^ t * M.Q θ γ t y u)
  have h₁₀ : ∫ ω, fderiv ℝ (fun θ' => M.V θ' γ n (s n ω)) θ ∂(M.traj θ) =
      ∑ y, (M.traj θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => M.V θ' γ n y) θ :=
    E_s1 M θ n (fun y => fderiv ℝ (fun θ' => M.V θ' γ n y) θ)
  rw [grad_obj M h₄ h₇ h₃ θ, Finset.sum_congr rfl fun x _ => h₈ x,
    integral_finsetSum _ fun t _ => integrable_sa M θ t
      (fun y u => (γ ^ t * M.Q θ γ t y u) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  simp_rw [h₉, h₁₀, P_eq M θ]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    Finset.sum_mul]
  congr 1
  · conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  · conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring


-- created on 2026-09-26
