import Lemma.Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Unrolled policy-gradient recursion: for a reachable initial state `x` (`h₆`) and every `n`,
`∇V(s[0] = x) = ∑ t < n, γ ^ t • ∑ y, Pr(s[t] = y | s[0] = x) • ∑ u, Q(y, u) • ∇π(u | y)
  + γ ^ n • ∑ y, Pr(s[n] = y | s[0] = x) • ∇V(s[n] = y)`.
The sympy path integral `∫ ∏ Pr(s[t+1] | s[t])` over `s[1:t+1]` is written as the `t`-step
conditional probability `Pr(s[t] = y | s[0] = x)` (Chapman–Kolmogorov).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {x : S}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : ∀ t, IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : ∀ θ t x u, Q θ t x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (h₂ : ∀ θ t x, V θ t x = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₃ : γ ∈ Set.Ico 0 1)
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₅ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖))
  (h₆ : (M.traj θ).real (s 0 ⁻¹' {x}) ≠ 0)
  (n : ℕ) :
-- imply
  fderiv ℝ (fun θ => V θ 0 x) θ =
    ∑ t ∈ Finset.range n, γ ^ t • ∑ y, ((M.traj θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) •
        ∑ u, Q θ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
      γ ^ n • ∑ y, ((M.traj θ)[|s 0 ⁻¹' {x}]).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ => V θ n y) θ := by
-- proof
  have hQ : Q = fun θ => M.Q θ γ :=
    funext fun θ => funext fun t => funext fun x => funext fun u => h₁ θ t x u
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => h₂ θ t x
  subst hQ hV
  obtain ⟨C, hC⟩ := id h₅
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce
  have h₈ : ∀ t y, ((M.traj θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
    have h := cond_Pn M θ 0 t x y h₆
    rwa [zero_add] at h
  simp_rw [h₈]
  induction n with
  | zero => simp [Pn_zero]
  | succ n ih =>
    have h₉ : ∀ y, M.Pn θ n x y • fderiv ℝ (fun θ => M.V θ γ n y) θ =
        M.Pn θ n x y • (∑ u, M.Q θ γ n y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
          γ • ∑ z, M.P1 θ y z • fderiv ℝ (fun θ => M.V θ γ (n + 1) z) θ) := by
      intro y
      by_cases hy : M.Pn θ n x y = 0
      · rw [hy, zero_smul, zero_smul]
      have hP := reach_n M θ n x y h₆ hy
      have h := Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion
        (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) (h₀ n) (fun _ _ _ _ => rfl)
        (fun _ _ _ => rfl) h₃ h₄ h₅ hP
      rw [h]
      simp_rw [cond_P1 M θ n y _ hP]
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => h₉ y]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    simp_rw [Pn_succ', Finset.sum_smul, Finset.smul_sum, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring


-- created on 2026-09-26
